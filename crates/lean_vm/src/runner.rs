use p3_field::BasedVectorSpace;
use p3_field::PrimeCharacteristicRing;
use p3_field::dot_product;
use p3_util::log2_ceil_usize;
use std::collections::BTreeMap;
use utils::ToUsize;
use utils::get_poseidon16;
use utils::get_poseidon24;
use utils::pretty_integer;
use whir_p3::poly::evals::EvaluationsList;
use whir_p3::poly::multilinear::MultilinearPoint;

use crate::lean_isa::*;
use crate::profiler::profiling_report;
use crate::stack_trace::pretty_stack_trace;
use crate::*;
use crate::error::RunnerError;
use p3_field::Field;
use p3_symmetric::Permutation;

const STACK_TRACE_INSTRUCTIONS: usize = 5000;

#[derive(Debug, Clone)]
pub struct RangeCheckInstrs {
    step_1: Instruction,
    step_2: Instruction,
    step_3: Instruction,
}

impl MemOrConstant {
    pub fn read_value(&self, memory: &Memory, fp: usize) -> Result<F, RunnerError> {
        match self {
            Self::Constant(c) => Ok(*c),
            Self::MemoryAfterFp { offset } => memory.get(fp + *offset),
        }
    }

    pub fn is_value_unknown(&self, memory: &Memory, fp: usize) -> bool {
        self.read_value(memory, fp).is_err()
    }

    pub const fn memory_address(&self, fp: usize) -> Result<usize, RunnerError> {
        match self {
            Self::Constant(_) => Err(RunnerError::NotAPointer),
            Self::MemoryAfterFp { offset } => Ok(fp + *offset),
        }
    }
}

impl MemOrFp {
    pub fn read_value(&self, memory: &Memory, fp: usize) -> Result<F, RunnerError> {
        match self {
            Self::MemoryAfterFp { offset } => memory.get(fp + *offset),
            Self::Fp => Ok(F::from_usize(fp)),
        }
    }

    pub fn is_value_unknown(&self, memory: &Memory, fp: usize) -> bool {
        self.read_value(memory, fp).is_err()
    }

    pub const fn memory_address(&self, fp: usize) -> Result<usize, RunnerError> {
        match self {
            Self::MemoryAfterFp { offset } => Ok(fp + *offset),
            Self::Fp => Err(RunnerError::NotAPointer),
        }
    }
}

impl MemOrFpOrConstant {
    pub fn read_value(&self, memory: &Memory, fp: usize) -> Result<F, RunnerError> {
        match self {
            Self::MemoryAfterFp { offset } => memory.get(fp + *offset),
            Self::Fp => Ok(F::from_usize(fp)),
            Self::Constant(c) => Ok(*c),
        }
    }

    pub fn is_value_unknown(&self, memory: &Memory, fp: usize) -> bool {
        self.read_value(memory, fp).is_err()
    }

    pub const fn memory_address(&self, fp: usize) -> Result<usize, RunnerError> {
        match self {
            Self::MemoryAfterFp { offset } => Ok(fp + *offset),
            Self::Fp => Err(RunnerError::NotAPointer),
            Self::Constant(_) => Err(RunnerError::NotAPointer),
        }
    }
}

#[derive(Debug, Clone, Default)]
pub(crate) struct ExecutionHistory {
    pub(crate) lines: Vec<LocationInSourceCode>,
    pub(crate) cycles: Vec<usize>, // for each line, how many cycles it took
}

fn print_execution_error(
    err: &RunnerError,
    std_out: &str,
    instruction_history: &ExecutionHistory,
    source_code: &str,
    function_locations: &BTreeMap<usize, String>,
) {
    let lines_history = &instruction_history.lines;
    let latest_instructions =
        &lines_history[lines_history.len().saturating_sub(STACK_TRACE_INSTRUCTIONS)..];
    println!(
        "\n{}",
        pretty_stack_trace(source_code, latest_instructions, function_locations)
    );
    if !std_out.is_empty() {
        println!("╔══════════════════════════════════════════════════════════════╗");
        println!("║                         STD-OUT                              ║");
        println!("╚══════════════════════════════════════════════════════════════╝\n");
        print!("{std_out}");
    }
    println!("Execution failed with error: {:?}", err);
}

pub fn execute_bytecode(
    bytecode: &mut Bytecode,
    public_input: &[F],
    private_input: &[F],
    source_code: &str,                            // debug purpose
    function_locations: &BTreeMap<usize, String>, // debug purpose
    profiler: bool,
) -> Result<ExecutionResult, RunnerError> {
    let mut std_out = String::new();
    let mut instruction_history = ExecutionHistory::default();
    let first_exec = match execute_bytecode_helper(
        bytecode,
        public_input,
        private_input,
        MAX_RUNNER_MEMORY_SIZE / 2,
        false,
        &mut std_out,
        &mut instruction_history,
        false,
        function_locations,
    ) {
        Ok(first_exec) => {
            println!("First execution: Ok");
            first_exec
        }
        Err(err) => {
            println!("First execution: Err");
            print_execution_error(&err, &std_out, &instruction_history, source_code, function_locations);
            return Err(err);
        }
    };

    println!("fps: {:?}\n", first_exec.fps);
    println!("ending_pc: {}", bytecode.ending_pc);
    println!("{}", bytecode);
    println!("\nSECOND EXEC: ----------------------------------");
    let fp = first_exec.fps[first_exec.fps.len() - 2];
    assert!(fp != 0, "final_nonzero_fp should not be 0");
    assert_eq!(first_exec.fps[first_exec.fps.len() - 1], 0, "The final fp should be 0");

    // If range-checks are present, add the actual 3-step range checks to the end of the bytecode.
    if first_exec.range_check_pcs.len() > 0 {
        let range_check_pcs = first_exec.range_check_pcs;
        let memory = first_exec.memory;

        let mut rc_new_instrs: Vec<Instruction> = Vec::with_capacity(&range_check_pcs.len() * 3);
        for pc in &range_check_pcs {
            let instr = bytecode.instructions[*pc].clone();
            match instr {
                Instruction::RangeCheck { value, max } => {
                    let v_usize = value.read_value(&memory, fp)?.to_usize();
                    let t_usize = max.read_value(&memory, fp)?.to_usize();

                    let x = match value {
                        MemOrFp::MemoryAfterFp { offset } => offset,
                        _ => unreachable!(),
                    };

                    let i = 0;

                    // If m[val] is undefined, deref m[fp + i] = m[val] will fail as m[fp + i] is
                    // also undefined. So we need to use z since m[fp + z] is 0.
                    // z may also come in handy for step 3.
                    let mut z = 0;
                    loop { 
                        let m_fp_z = memory.get(fp + z);
                        if m_fp_z.is_err() {
                            z += 1;
                            continue;
                        }
                        if m_fp_z.unwrap() == F::ZERO { break; }
                        z += 1;
                    }

                    // Step 1: use deref with m[m[fp + x]] to force an OOM if val >= M
                    // Find z such that m[fp + z] = 0
                    let step_1_offset = if matches!(memory.get(v_usize), Err(RunnerError::UndefinedMemory)) {
                        z
                    } else {
                        i // Otherwise, use i
                    };

                    let step_1 = Instruction::Deref {
                        shift_0: x,
                        shift_1: 0,
                        res: MemOrFpOrConstant::MemoryAfterFp { offset: step_1_offset },
                    };

                    // Step 2: (t - 1) = m[fp + j] + m[m[fp + x]]
                    // Find j such that m[fp + j] is undefined
                    let mut j = step_1_offset + 1;
                    loop {
                        let m_fp_j = memory.get(fp + j);
                        if m_fp_j.is_err() && matches!(m_fp_j, Err(RunnerError::UndefinedMemory)) {
                            break
                        }
                        j += 1;
                    }

                    let step_2 = Instruction::Computation {
                        operation: Operation::Add,
                        arg_a: MemOrConstant::MemoryAfterFp { offset: j },        // Unknown
                        arg_c: MemOrFp::MemoryAfterFp { offset: x },              // Known
                        res: MemOrConstant::Constant(F::from_usize(t_usize - 1)), // Known
                    };

                    // Step 3
                    // deref: m[m[fp + j]] = m[fp + k]
                    // if m[m[fp + j]] is uninitialized, then m[fp + k] must be 0, so we need to
                    // find a memory cell that contains 0.
                    // can use z for k.
                    let m_fp_j = memory.get(
                        (F::from_usize(t_usize) - F::ONE - F::from_usize(v_usize)).to_usize(),
                    );

                    let k = if m_fp_j.is_err() && matches!(m_fp_j, Err(RunnerError::UndefinedMemory)) {
                        z
                    } else {
                        // Otherwise, find an uninitialized memory cell
                        let mut k = j + 1;
                        loop {
                            let m_fp_k = memory.get(fp + k);
                            if k != x && m_fp_k.is_err() && matches!(m_fp_k, Err(RunnerError::UndefinedMemory)) {
                                break
                            }
                            k += 1;
                        }
                        k
                    };
                    println!("i = {}, j = {}, k = {}", i, j, k);
                    let step_3 = Instruction::Deref {
                        shift_0: j,
                        shift_1: 0,
                        res: MemOrFpOrConstant::MemoryAfterFp { offset: k },
                    };

                    rc_new_instrs.push(step_1);
                    rc_new_instrs.push(step_2);
                    rc_new_instrs.push(step_3);
                }
                _ => continue
            }
        }

        for new_instr in rc_new_instrs {
            bytecode.instructions.insert(bytecode.instructions.len() - 2, new_instr);
            bytecode.ending_pc += 1;
        }

        // Update the final 2 jump instructions
        let num_instructions = bytecode.instructions.len();
        let final_jump = bytecode.instructions[bytecode.ending_pc - 1].clone();
        let final_jump_2 = bytecode.instructions[bytecode.ending_pc - 0].clone();

        assert!(matches!(final_jump, Instruction::Jump { .. }));
        assert!(matches!(final_jump_2, Instruction::Jump { .. }));

        let final_jump = Instruction::Jump {
            condition: MemOrConstant::one(),
            dest: MemOrConstant::Constant(F::from_usize(num_instructions - 1)),
            updated_fp: MemOrFp::Fp,
        };

        bytecode.instructions[num_instructions - 2] = final_jump.clone();
        bytecode.instructions[num_instructions - 1] = final_jump.clone();

        println!("Bytecode after adding range checks:");
        println!("{}", bytecode);
        println!("ending_pc: {}", bytecode.ending_pc);
    } else {
        println!("No range checks found");
    }

    instruction_history = ExecutionHistory::default();
    let second_exec = match execute_bytecode_helper(
        bytecode,
        public_input,
        private_input,
        first_exec.no_vec_runtime_memory,
        true,
        &mut String::new(),
        &mut instruction_history,
        profiler,
        function_locations,
    ) {
        Ok(second_exec) => {
            println!("Second execution: Ok\n----------------------------------\n");
            Ok(second_exec)
        }
        Err(err) => {
            println!("Second execution: Err");
            print_execution_error(&err, &std_out, &instruction_history, source_code, function_locations);

            return Err(err);
        }
    };
    second_exec
}

#[derive(Debug)]
pub struct ExecutionResult {
    pub no_vec_runtime_memory: usize,
    pub public_memory_size: usize,
    pub memory: Memory,
    pub pcs: Vec<usize>,
    pub fps: Vec<usize>,
    pub range_check_pcs: Vec<usize>,
}

pub fn build_public_memory(public_input: &[F]) -> Vec<F> {
    // padded to a power of two
    let public_memory_len = (PUBLIC_INPUT_START + public_input.len()).next_power_of_two();
    let mut public_memory = F::zero_vec(public_memory_len);
    public_memory[PUBLIC_INPUT_START..][..public_input.len()].copy_from_slice(public_input);

    // "zero" vector
    let zero_start = ZERO_VEC_PTR * VECTOR_LEN;
    for slot in public_memory
        .iter_mut()
        .skip(zero_start)
        .take(2 * VECTOR_LEN)
    {
        *slot = F::ZERO;
    }

    // "one" vector
    public_memory[ONE_VEC_PTR * VECTOR_LEN] = F::ONE;
    let one_start = ONE_VEC_PTR * VECTOR_LEN + 1;
    for slot in public_memory
        .iter_mut()
        .skip(one_start)
        .take(VECTOR_LEN - 1)
    {
        *slot = F::ZERO;
    }

    public_memory
        [POSEIDON_16_NULL_HASH_PTR * VECTOR_LEN..(POSEIDON_16_NULL_HASH_PTR + 2) * VECTOR_LEN]
        .copy_from_slice(&get_poseidon16().permute([F::ZERO; 16]));
    public_memory
        [POSEIDON_24_NULL_HASH_PTR * VECTOR_LEN..(POSEIDON_24_NULL_HASH_PTR + 1) * VECTOR_LEN]
        .copy_from_slice(&get_poseidon24().permute([F::ZERO; 24])[16..]);
    public_memory
}

#[allow(clippy::too_many_arguments)] // TODO
fn execute_bytecode_from(
    bytecode: &Bytecode,
    memory: &mut Memory,
    no_vec_runtime_memory: usize,
    final_execution: bool,
    std_out: &mut String,
    instruction_history: &mut ExecutionHistory,
    profiler: bool,
    function_locations: &BTreeMap<usize, String>,
) {
}


#[allow(clippy::too_many_arguments)] // TODO
fn execute_bytecode_helper(
    bytecode: &Bytecode,
    public_input: &[F],
    private_input: &[F],
    no_vec_runtime_memory: usize,
    final_execution: bool,
    std_out: &mut String,
    instruction_history: &mut ExecutionHistory,
    profiler: bool,
    function_locations: &BTreeMap<usize, String>,
) -> Result<ExecutionResult, RunnerError> {
    let poseidon_16 = get_poseidon16();
    let poseidon_24 = get_poseidon24();

    // set public memory
    let mut memory = Memory::new(build_public_memory(public_input));
    let public_memory_size = (PUBLIC_INPUT_START + public_input.len()).next_power_of_two();
    let mut fp = public_memory_size;

    for (i, value) in private_input.iter().enumerate() {
        memory.set(fp + i, *value)?;
    }
    //for (i, m) in memory.0.iter().enumerate() {
        //println!("m[{}]: {:?}", i, m);
    //}

    fp += private_input.len();
    fp = fp.next_multiple_of(DIMENSION);

    let initial_ap = fp + bytecode.starting_frame_memory;
    let initial_ap_vec =
        (initial_ap + no_vec_runtime_memory).next_multiple_of(VECTOR_LEN) / VECTOR_LEN;

    let mut pc = 0;
    let mut ap = initial_ap;
    let mut ap_vec = initial_ap_vec;

    let mut poseidon16_calls = 0;
    let mut poseidon24_calls = 0;
    let mut dot_product_ext_ext_calls = 0;
    let mut multilinear_eval_calls = 0;
    let mut cpu_cycles = 0;

    let mut last_checkpoint_cpu_cycles = 0;
    let mut checkpoint_ap = initial_ap;
    let mut checkpoint_ap_vec = ap_vec;

    let mut pcs = Vec::new();
    let mut fps = Vec::new();

    let mut add_counts = 0;
    let mut mul_counts = 0;
    let mut deref_counts = 0;
    let mut jump_counts = 0;

    let mut counter_hint = 0;
    let mut cpu_cycles_before_new_line = 0;

    let mut range_check_pcs: Vec<usize> = Vec::new();

    while pc != bytecode.ending_pc {
        println!("pc: {}", pc);
        if pc >= bytecode.instructions.len() {
            return Err(RunnerError::PCOutOfBounds);
        }

        pcs.push(pc);
        fps.push(fp);

        cpu_cycles += 1;
        cpu_cycles_before_new_line += 1;

        for hint in bytecode.hints.get(&pc).unwrap_or(&vec![]) {
            match hint {
                Hint::RequestMemory {
                    offset,
                    size,
                    vectorized,
                    vectorized_len,
                } => {
                    let size = size.read_value(&memory, fp)?.to_usize();

                    if *vectorized {
                        assert!(*vectorized_len >= LOG_VECTOR_LEN, "TODO");

                        // padding:
                        while !(ap_vec * VECTOR_LEN).is_multiple_of(1 << *vectorized_len) {
                            ap_vec += 1;
                        }
                        memory.set(
                            fp + *offset,
                            F::from_usize(ap_vec >> (*vectorized_len - LOG_VECTOR_LEN)),
                        )?;
                        ap_vec += size << (*vectorized_len - LOG_VECTOR_LEN);
                    } else {
                        memory.set(fp + *offset, F::from_usize(ap))?;
                        ap += size;
                    }
                    // does not increase PC
                }
                Hint::DecomposeBits {
                    res_offset,
                    to_decompose,
                } => {
                    let mut memory_index = fp + *res_offset;
                    for value_source in to_decompose {
                        let value = value_source.read_value(&memory, fp)?.to_usize();
                        for i in 0..F::bits() {
                            let bit = F::from_bool(value & (1 << i) != 0);
                            memory.set(memory_index, bit)?;
                            memory_index += 1;
                        }
                    }
                }
                Hint::CounterHint { res_offset } => {
                    memory.set(fp + *res_offset, F::from_usize(counter_hint))?;
                    counter_hint += 1;
                }
                Hint::Inverse { arg, res_offset } => {
                    let value = arg.read_value(&memory, fp)?;
                    let result = value.try_inverse().unwrap_or(F::ZERO);
                    memory.set(fp + *res_offset, result)?;
                }
                Hint::Print { line_info, content } => {
                    let values = content
                        .iter()
                        .map(|value| Ok(value.read_value(&memory, fp)?.to_string()))
                        .collect::<Result<Vec<_>, _>>()?;
                    // Logs for performance analysis:
                    if values[0] == "123456789" {
                        if values.len() == 1 {
                            *std_out += "[CHECKPOINT]\n";
                        } else {
                            assert_eq!(values.len(), 2);
                            let new_no_vec_memory = ap - checkpoint_ap;
                            let new_vec_memory = (ap_vec - checkpoint_ap_vec) * DIMENSION;
                            *std_out += &format!(
                                "[CHECKPOINT {}] new CPU cycles: {}, new runtime memory: {} ({:.1}% vec)\n",
                                values[1],
                                pretty_integer(cpu_cycles - last_checkpoint_cpu_cycles),
                                pretty_integer(new_no_vec_memory + new_vec_memory),
                                new_vec_memory as f64 / (new_no_vec_memory + new_vec_memory) as f64
                                    * 100.0
                            );
                        }

                        last_checkpoint_cpu_cycles = cpu_cycles;
                        checkpoint_ap = ap;
                        checkpoint_ap_vec = ap_vec;
                        continue;
                    }

                    let line_info = line_info.replace(';', "");
                    *std_out += &format!("\"{}\" -> {}\n", line_info, values.join(", "));
                    // does not increase PC
                }
                Hint::LocationReport { location } => {
                    instruction_history.lines.push(*location);
                    instruction_history.cycles.push(cpu_cycles_before_new_line);
                    cpu_cycles_before_new_line = 0;
                }
            }
        }

        let instruction = &bytecode.instructions[pc];
        match instruction {
            Instruction::Computation {
                operation,
                arg_a,
                arg_c,
                res,
            } => {
                if res.is_value_unknown(&memory, fp) {
                    let memory_address_res = res.memory_address(fp)?;
                    let a_value = arg_a.read_value(&memory, fp)?;
                    let b_value = arg_c.read_value(&memory, fp)?;
                    let res_value = operation.compute(a_value, b_value);
                    memory.set(memory_address_res, res_value)?;
                } else if arg_a.is_value_unknown(&memory, fp) {
                    let memory_address_a = arg_a.memory_address(fp)?;
                    let res_value = res.read_value(&memory, fp)?;
                    let b_value = arg_c.read_value(&memory, fp)?;
                    let a_value = operation
                        .inverse_compute(res_value, b_value)
                        .ok_or(RunnerError::DivByZero)?;
                    memory.set(memory_address_a, a_value)?;
                } else if arg_c.is_value_unknown(&memory, fp) {
                    let memory_address_b = arg_c.memory_address(fp)?;
                    let res_value = res.read_value(&memory, fp)?;
                    let a_value = arg_a.read_value(&memory, fp)?;
                    let b_value = operation
                        .inverse_compute(res_value, a_value)
                        .ok_or(RunnerError::DivByZero)?;
                    memory.set(memory_address_b, b_value)?;
                } else {
                    let a_value = arg_a.read_value(&memory, fp)?;
                    let b_value = arg_c.read_value(&memory, fp)?;
                    let res_value = res.read_value(&memory, fp)?;
                    let computed_value = operation.compute(a_value, b_value);
                    if res_value != computed_value {
                        return Err(RunnerError::NotEqual(computed_value, res_value));
                    }
                }

                match operation {
                    Operation::Add => add_counts += 1,
                    Operation::Mul => mul_counts += 1,
                }

                pc += 1;
            }
            Instruction::Deref {
                shift_0,
                shift_1,
                res,
            } => {
                if res.is_value_unknown(&memory, fp) {
                    println!("unknown");
                    let memory_address_res = res.memory_address(fp)?;
                    let ptr = memory.get(fp + shift_0)?;
                    println!("ptr = m[fp + shift_0]: m[{} + {}] = {}", fp, shift_0, ptr);
                    println!("memory.get(ptr.to_usize() + shift_1)");
                    let value = memory.get(ptr.to_usize() + shift_1)?;
                    memory.set(memory_address_res, value)?;
                } else {
                    println!("known");
                    let value = res.read_value(&memory, fp)?;
                    let ptr = memory.get(fp + shift_0)?;
                    println!("ptr = fp + shift_0: {} + {} = {}", fp, shift_0, ptr);
                    memory.set(ptr.to_usize() + shift_1, value)?;
                }

                deref_counts += 1;
                pc += 1;
            }
            Instruction::Jump {
                condition,
                dest,
                updated_fp,
            } => {
                let condition_value = condition.read_value(&memory, fp)?;
                assert!([F::ZERO, F::ONE].contains(&condition_value),);
                if condition_value == F::ZERO {
                    pc += 1;
                } else {
                    pc = dest.read_value(&memory, fp)?.to_usize();
                    fp = updated_fp.read_value(&memory, fp)?.to_usize();
                }

                jump_counts += 1;
            }
            // The second execution should not contain any range checks
            // because after the first execution, which figures out which aux values to set,
            // the runner will replace Instruction::RangeCheck instances with the actual 3-step
            // range check instructions (deref, add, and deref)
            Instruction::RangeCheck { .. } => {
                // The runner should OOM at step 1 or step 3 if value >= max. See section 2.5.3 of
                // minimal_zkVM.pdf.
                range_check_pcs.push(pc);
                pc += 1;
            }
            Instruction::Poseidon2_16 { arg_a, arg_b, res } => {
                poseidon16_calls += 1;

                let a_value = arg_a.read_value(&memory, fp)?;
                let b_value = arg_b.read_value(&memory, fp)?;
                let res_value = res.read_value(&memory, fp)?;

                let arg0 = memory.get_vector(a_value.to_usize())?;
                let arg1 = memory.get_vector(b_value.to_usize())?;

                let mut input = [F::ZERO; VECTOR_LEN * 2];
                input[..VECTOR_LEN].copy_from_slice(&arg0);
                input[VECTOR_LEN..].copy_from_slice(&arg1);

                poseidon_16.permute_mut(&mut input);

                let res0: [F; VECTOR_LEN] = input[..VECTOR_LEN].try_into().unwrap();
                let res1: [F; VECTOR_LEN] = input[VECTOR_LEN..].try_into().unwrap();

                memory.set_vector(res_value.to_usize(), res0)?;
                memory.set_vector(1 + res_value.to_usize(), res1)?;

                pc += 1;
            }
            Instruction::Poseidon2_24 { arg_a, arg_b, res } => {
                poseidon24_calls += 1;

                let a_value = arg_a.read_value(&memory, fp)?;
                let b_value = arg_b.read_value(&memory, fp)?;
                let res_value = res.read_value(&memory, fp)?;

                let arg0 = memory.get_vector(a_value.to_usize())?;
                let arg1 = memory.get_vector(1 + a_value.to_usize())?;
                let arg2 = memory.get_vector(b_value.to_usize())?;

                let mut input = [F::ZERO; VECTOR_LEN * 3];
                input[..VECTOR_LEN].copy_from_slice(&arg0);
                input[VECTOR_LEN..2 * VECTOR_LEN].copy_from_slice(&arg1);
                input[2 * VECTOR_LEN..].copy_from_slice(&arg2);

                poseidon_24.permute_mut(&mut input);

                let res: [F; VECTOR_LEN] = input[2 * VECTOR_LEN..].try_into().unwrap();

                memory.set_vector(res_value.to_usize(), res)?;

                pc += 1;
            }
            Instruction::DotProductExtensionExtension {
                arg0,
                arg1,
                res,
                size,
            } => {
                dot_product_ext_ext_calls += 1;

                let ptr_arg_0 = arg0.read_value(&memory, fp)?.to_usize();
                let ptr_arg_1 = arg1.read_value(&memory, fp)?.to_usize();
                let ptr_res = res.read_value(&memory, fp)?.to_usize();

                let slice_0 = memory.get_continuous_slice_of_ef_elements(ptr_arg_0, *size)?;
                let slice_1 = memory.get_continuous_slice_of_ef_elements(ptr_arg_1, *size)?;

                let dot_product = dot_product::<EF, _, _>(slice_0.into_iter(), slice_1.into_iter());
                memory.set_ef_element(ptr_res, dot_product)?;

                pc += 1;
            }
            Instruction::MultilinearEval {
                coeffs,
                point,
                res,
                n_vars,
            } => {
                multilinear_eval_calls += 1;

                let ptr_coeffs = coeffs.read_value(&memory, fp)?.to_usize();
                let ptr_point = point.read_value(&memory, fp)?.to_usize();
                let ptr_res = res.read_value(&memory, fp)?.to_usize();
                let n_coeffs = 1 << *n_vars;
                let slice_coeffs = memory.slice(ptr_coeffs << *n_vars, n_coeffs)?;

                let log_point_size = log2_ceil_usize(*n_vars * DIMENSION);
                let point_slice = memory.slice(ptr_point << log_point_size, *n_vars * DIMENSION)?;
                for i in *n_vars * DIMENSION..(*n_vars * DIMENSION).next_power_of_two() {
                    memory.set((ptr_point << log_point_size) + i, F::ZERO)?; // padding
                }
                let point = point_slice[..*n_vars * DIMENSION]
                    .chunks_exact(DIMENSION)
                    .map(|chunk| EF::from_basis_coefficients_slice(chunk).unwrap())
                    .collect::<Vec<_>>();

                let eval = slice_coeffs.evaluate(&MultilinearPoint(point));
                let mut res_vec = eval.as_basis_coefficients_slice().to_vec();
                res_vec.resize(VECTOR_LEN, F::ZERO);
                memory.set_vector(ptr_res, res_vec.try_into().unwrap())?;

                pc += 1;
            }
        }
    }

    debug_assert_eq!(pc, bytecode.ending_pc);
    pcs.push(pc);
    fps.push(fp);

    if final_execution {
        if profiler {
            let report = profiling_report(instruction_history, function_locations);
            println!("\n{report}");
        }
        if !std_out.is_empty() {
            println!("╔═════════════════════════════════════════════════════════════════════════╗");
            println!("║                                STD-OUT                                  ║");
            println!("╚═════════════════════════════════════════════════════════════════════════╝");
            print!("\n{std_out}");
            println!(
                "──────────────────────────────────────────────────────────────────────────\n"
            );
        }

        println!("╔═════════════════════════════════════════════════════════════════════════╗");
        println!("║                                 STATS                                   ║");
        println!("╚═════════════════════════════════════════════════════════════════════════╝\n");

        println!("CYCLES: {}", pretty_integer(cpu_cycles));
        println!("MEMORY: {}", pretty_integer(memory.0.len()));
        println!();

        let runtime_memory_size = memory.0.len() - (PUBLIC_INPUT_START + public_input.len());
        println!(
            "Bytecode size: {}",
            pretty_integer(bytecode.instructions.len())
        );
        println!("Public input size: {}", pretty_integer(public_input.len()));
        println!(
            "Private input size: {}",
            pretty_integer(private_input.len())
        );
        println!(
            "Runtime memory: {} ({:.2}% vec)",
            pretty_integer(runtime_memory_size),
            (DIMENSION * (ap_vec - initial_ap_vec)) as f64 / runtime_memory_size as f64 * 100.0
        );
        let used_memory_cells = memory
            .0
            .iter()
            .skip(PUBLIC_INPUT_START + public_input.len())
            .filter(|&&x| x.is_some())
            .count();
        println!(
            "Memory usage: {:.1}%",
            used_memory_cells as f64 / runtime_memory_size as f64 * 100.0
        );

        println!();

        if poseidon16_calls + poseidon24_calls > 0 {
            println!(
                "Poseidon2_16 calls: {}, Poseidon2_24 calls: {} (1 poseidon per {} instructions)",
                pretty_integer(poseidon16_calls),
                pretty_integer(poseidon24_calls),
                cpu_cycles / (poseidon16_calls + poseidon24_calls)
            );
        }
        if dot_product_ext_ext_calls > 0 {
            println!(
                "DotProduct calls: {}",
                pretty_integer(dot_product_ext_ext_calls)
            );
        }
        if multilinear_eval_calls > 0 {
            println!(
                "MultilinearEval calls: {}",
                pretty_integer(multilinear_eval_calls)
            );
        }

        if false {
            println!("Low level instruction counts:");
            println!(
                "COMPUTE: {} ({} ADD, {} MUL)",
                add_counts + mul_counts,
                add_counts,
                mul_counts
            );
            println!("DEREF: {deref_counts}");
            println!("JUMP: {jump_counts}");
        }

        println!("──────────────────────────────────────────────────────────────────────────\n");
    }

    let no_vec_runtime_memory = ap - initial_ap;

    return Ok(ExecutionResult {
        no_vec_runtime_memory,
        public_memory_size,
        memory,
        pcs,
        fps,
        range_check_pcs,
    });
}

///// Replace elements at `indices` with corresponding `repls` (same length).
///// Indices may be unsorted; duplicates or OOB will error.
//fn splice_many<T: Clone>(
    //base: &[T],
    //indices: &[usize],
    //repls: &[&[T]],
//) -> Result<Vec<T>, &'static str> {
    //if indices.len() != repls.len() {
        //return Err("indices and repls must have the same length");
    //}

    //let mut pairs: Vec<(usize, &[T])> = indices.iter().cloned().zip(repls.iter().cloned()).collect();
    //pairs.sort_by_key(|p| p.0);

    //for w in pairs.windows(2) {
        //if w[0].0 == w[1].0 { return Err("duplicate index"); }
    //}
    //if pairs.iter().any(|(i, _)| *i >= base.len()) {
        //return Err("index out of bounds");
    //}

    //let extra = pairs.iter().map(|(_, r)| r.len()).sum::<usize>() as isize
        //- pairs.len() as isize;
    //let cap = (base.len() as isize + extra).max(0) as usize;

    //let mut out = Vec::with_capacity(cap);
    //let mut it = pairs.into_iter().peekable();

    //for (i, item) in base.iter().enumerate() {
        //if let Some(&(idx, repl)) = it.peek() {
            //if idx == i {
                //out.extend_from_slice(repl); // insert replacement
                //it.next();                   // consume this pair
                //continue;                    // skip original element at i
            //}
        //}
        //out.push(item.clone());
    //}
    //Ok(out)
//}

//#[test]
//fn test_splice_many() {
    //let a = [1, 2, 3, 4, 5];
    //let indices = [1, 3];                   // positions to replace
    //let c1 = [8];
    //let c2 = [9];
    //let repls: &[&[i32]] = &[&c1, &c2];

    //let out = splice_many(&a, &indices, repls).unwrap();
    //assert_eq!(out, vec![1, 8, 3, 9, 5]);
//}
