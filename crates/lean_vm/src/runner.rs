use std::collections::{ BTreeMap, BTreeSet };
use whir_p3::poly::evals::EvaluationsList;
use whir_p3::poly::multilinear::MultilinearPoint;
use p3_util::log2_ceil_usize;
use p3_symmetric::Permutation;
use p3_field::{ BasedVectorSpace, PrimeCharacteristicRing, dot_product, Field };

use crate::*;
use crate::lean_isa::*;
use crate::error::RunnerError;
use crate::profiler::profiling_report;
use crate::stack_trace::pretty_stack_trace;
use utils::{ ToUsize, get_poseidon16, get_poseidon24, pretty_integer, Poseidon16, Poseidon24};

const STACK_TRACE_INSTRUCTIONS: usize = 5000;

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
pub struct ExecutionHistory {
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

fn find_next_zero_cell(memory: &Memory, start_offset: usize) -> Option<usize> {
    if start_offset >= memory.0.len() {
        return None;
    }
    let mut z = start_offset;

    loop { 
        if z >= memory.0.len() {
            break;
        }
        let m_fp_z = &memory.get(z);
        if !m_fp_z.is_err() && m_fp_z.clone().unwrap() == F::ZERO {
            return Some(z)
        }
        z += 1;
    }
    None
}

fn find_next_undefined_cell_from_mem(
    mem: &Memory,
    conflicts: &BTreeSet<usize>,
    pos: usize,
) -> usize {
    let mut z = pos;

    while !matches!(mem.get(z), Err(RunnerError::UndefinedMemory)) {
        z += 1;
    }

    loop {
        if conflicts.contains(&z) {
            z = find_next_undefined_cell_from_mem(mem, conflicts, z + 1);
        } else {
            break;
        }
    }
    z
}

pub fn is_undef(mem: &Memory, pos: usize) -> bool {
    matches!(mem.get(pos), Err(RunnerError::UndefinedMemory))
}

#[derive(Debug, Clone)]
struct RangeCheckInfo {
    hint_fp: usize,
    v_pos: usize,
    v: usize,
    t: usize,
    q: usize, // t - 1 - v
}

pub fn compile_range_checks(
    first_exec: &ExecutionResult,
    bytecode: &Bytecode,
) -> Result<Bytecode, RunnerError> {
    // Early return if no range checks exist
    if !bytecode.hints.values().any(|hints| 
        hints.iter().any(|h| matches!(h, Hint::RangeCheck { .. }))
    ) {
        return Ok(bytecode.clone());
    }

    // Convenience mapping: instr_idx -> RangeCheckInfo
    let mut rcs: BTreeMap<(usize, usize), RangeCheckInfo> = BTreeMap::new();

    // Validate that the last fp is 0
    let last_fp = first_exec.fps.last()
        .ok_or(RunnerError::PCOutOfBounds)?; // Using existing error type
    if *last_fp != 0 {
        return Err(RunnerError::PCOutOfBounds); // Using existing error type for now
    }

    // Find the penultimate instruction
    let pen_instr = bytecode.instructions[first_exec.pcs[first_exec.pcs.len() - 2]].clone();

    // Assume that the penultimate instruction is a JUMP
    assert!(matches!(pen_instr, Instruction::Jump { .. }));

    // Assume that the destination of the penultimate jump is the last instruction
    match pen_instr {
        Instruction::Jump { dest, .. } => {
            match dest {
                MemOrConstant::Constant(c) => {
                    assert_eq!(c.to_usize(), first_exec.pcs[first_exec.pcs.len() - 1]);
                }
                MemOrConstant::MemoryAfterFp { .. } => {
                    unreachable!();
                }
            }
        }
        _ => {}
    }

    // Keep track of memory locations we will write to
    let mut conflicts: BTreeSet<usize> = BTreeSet::new();

    for (pc, hints) in &bytecode.hints {
        for (hint_idx, hint) in hints.iter().enumerate() {
            match hint {
                Hint::RangeCheck { value, max } => {
                    let v_off = match value {
                        MemOrFp::MemoryAfterFp { offset } => *offset,
                        MemOrFp::Fp => 0, // fp is at offset 0
                    };
                    let execution_step = first_exec.pcs.iter().position(|&p| p == *pc).unwrap();
                    let hint_fp = first_exec.fps[execution_step];
                    let v_pos = hint_fp + v_off;
                    let v = first_exec.memory.get(v_pos).unwrap().to_usize();
                    let t = match max {
                        MemOrConstant::MemoryAfterFp { .. } => {
                            unreachable!();
                        }
                        MemOrConstant::Constant(c) => {
                            c.to_usize()
                        }
                    };

                    // q = t - 1 - v in the field
                    let q = (F::from_usize(t) - F::ONE - F::from_usize(v)).to_usize();

                    rcs.insert((*pc, hint_idx), RangeCheckInfo {
                        hint_fp,
                        v_pos,
                        v,
                        t,
                        q,
                    });

                    conflicts.insert(v);
                    conflicts.insert(t);
                }
                _ => {}
            }
        }
    }

    // Since the range check vals are referenced by offset, our fp must be the smallest possible
    // value: 0.
    let fp = 0;
    
    let mut instrs_to_insert: Vec<Instruction> = vec![];

    // Look for any 0 cells past fp, or create one
    let z_pos = find_next_zero_cell(&first_exec.memory, fp)
        .unwrap_or_else(|| {
            let z_pos = find_next_undefined_cell_from_mem(&first_exec.memory, &conflicts, fp);
            if first_exec.memory.get(z_pos).is_err() {
                let z_instr = Instruction::Computation {
                    operation: Operation::Add,
                    arg_a: MemOrConstant::Constant(F::ZERO),
                    arg_c: MemOrFp::MemoryAfterFp { offset: z_pos - fp },
                    res: MemOrConstant::Constant(F::ZERO),
                };
                instrs_to_insert.push(z_instr);
            }
            z_pos
        });

    conflicts.insert(z_pos);

    for ((_pc, _hint_idx), rc_info) in &rcs {
        // Step 1: DEREF m[m[fp + x]] == m[fp + i]
        let i = if is_undef(&first_exec.memory, rc_info.v) {
            // if m[v] is undefined, use z
            z_pos
        } else {
            // if m[v] is defined, then search for an i where m[fp + i] is undefined
            find_next_undefined_cell_from_mem(&first_exec.memory, &conflicts, fp)
        };
        let step_1 = Instruction::Deref {
            shift_0: rc_info.v_pos - fp,
            shift_1: 0,
            res: MemOrFpOrConstant::MemoryAfterFp { offset: i - fp },
        };

        // Since the step 1 deref writes to m[i], add i to conflicts
        conflicts.insert(i);

        // Step 2: ADD m[fp + j] = t - 1 - v
        let j = find_next_undefined_cell_from_mem(&first_exec.memory, &conflicts, i);
        let step_2 = Instruction::Computation {
            operation: Operation::Add,
            arg_a: MemOrConstant::Constant(F::ZERO), // 0
            arg_c: MemOrFp::MemoryAfterFp { offset: j - fp }, // Unknown; solves to t - 1 - v
            res: MemOrConstant::Constant(F::from_usize(rc_info.q)), // t - 1 - v
        };

        // Since the step 2 add writes to m[j], add j to conflicts
        conflicts.insert(j);

        // Step 3: DEREF m[fp + k] = m[m[fp + j]]
        let k = if is_undef(&first_exec.memory, rc_info.q) && !conflicts.contains(&rc_info.q) {
            // if m[q] is undefined, use z
            z_pos
        } else {
            // if m[q] is defined, then search for an k where m[fp + k] is undefined
            find_next_undefined_cell_from_mem(&first_exec.memory, &conflicts, j)
        };

        let step_3 = Instruction::Deref {
            shift_0: j - fp,
            shift_1: 0,
            res: MemOrFpOrConstant::MemoryAfterFp { offset: k - fp },
        };

        // Since the step 3 deref may write to m[k] or m[q], add q and k to conflicts
        conflicts.insert(k);
        conflicts.insert(rc_info.q);

        instrs_to_insert.push(step_1);
        instrs_to_insert.push(step_2);
        instrs_to_insert.push(step_3);
    }

    // Create the updated bytecode with range check instructions appended at the end
    let mut updated_bytecode = bytecode.clone();
    
    // Find the index of the penultimate instruction in the instruction list
    let penultimate_pc = first_exec.pcs[first_exec.pcs.len() - 2];
    
    // Append the range check instructions to the end
    let first_range_check_pc = updated_bytecode.instructions.len();
    updated_bytecode.instructions.extend(instrs_to_insert);
    
    // Add a final jump that terminates execution
    updated_bytecode.instructions.push(Instruction::Jump {
        condition: MemOrConstant::Constant(F::ZERO), // Never jump - terminates execution
        dest: MemOrConstant::Constant(F::ZERO), // Doesn't matter since condition is false
        updated_fp: MemOrFp::Fp,
    });
    
    // Update the penultimate jump to point to the first range check instruction
    if let Instruction::Jump { dest, .. } = &mut updated_bytecode.instructions[penultimate_pc] {
        *dest = MemOrConstant::Constant(F::from_usize(first_range_check_pc));
    }
    
    // Update ending_pc to point after the final jump
    updated_bytecode.ending_pc = updated_bytecode.instructions.len();
    
    Ok(updated_bytecode)
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
            first_exec
        }
        Err(err) => {
            print_execution_error(&err, &std_out, &instruction_history, source_code, function_locations);
            return Err(err);
        }
    };

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
            Ok(second_exec)
        }
        Err(err) => {
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
    pub initial_memory: Memory,
    pub pcs: Vec<usize>,
    pub fps: Vec<usize>,
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

#[allow(clippy::too_many_arguments)]
pub fn execute_bytecode_helper(
    bytecode: &Bytecode,
    public_input: &[F],
    private_input: &[F],
    no_vec_runtime_memory: usize,
    should_print_exec_stats: bool,
    std_out: &mut String,
    instruction_history: &mut ExecutionHistory,
    profiler: bool,
    function_locations: &BTreeMap<usize, String>,
) -> Result<ExecutionResult, RunnerError> {
    let mut state = State::init(bytecode, public_input, private_input, no_vec_runtime_memory)?;
    let initial_memory = state.memory.clone();

    while state.pc != bytecode.ending_pc {
        if state.pc >= bytecode.instructions.len() {
            return Err(RunnerError::PCOutOfBounds);
        }

        state.debug_state.pcs.push(state.pc);
        state.debug_state.fps.push(state.fp);

        state.debug_state.cpu_cycles += 1;
        state.debug_state.cpu_cycles_before_new_line += 1;

        let hints = bytecode.hints.get(&state.pc).unwrap_or(&vec![]).clone();
        let should_continue = execute_hints(
            &mut state,
            &hints,
            std_out,
            instruction_history,
        )?;
        
        if should_continue {
            continue;
        }

        let instruction = &bytecode.instructions[state.pc];
        //println!("fp: {}; exec pc: {}; instr: {}", state.fp, state.pc, instruction);
        //if hints.len() > 0 {
            //println!("hints: {:?}", hints);
        //}
        execute_instruction(&mut state, instruction)?;
    }

    assert_eq!(state.pc, bytecode.ending_pc);
    state.debug_state.pcs.push(state.pc);
    state.debug_state.fps.push(state.fp);

    if should_print_exec_stats {
        print_execution_stats(
            &state,
            bytecode,
            public_input,
            private_input,
            std_out,
            instruction_history,
            function_locations,
            profiler,
        );
    }

    let no_vec_runtime_memory = state.ap - state.initial_ap;

    return Ok(ExecutionResult {
        no_vec_runtime_memory,
        public_memory_size: state.public_memory_size,
        memory: state.memory,
        initial_memory,
        pcs: state.debug_state.pcs,
        fps: state.debug_state.fps,
    });
}

fn print_execution_stats(
    state: &State,
    bytecode: &Bytecode,
    public_input: &[F],
    private_input: &[F],
    std_out: &str,
    instruction_history: &ExecutionHistory,
    function_locations: &BTreeMap<usize, String>,
    profiler: bool,
) {
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

    println!("CYCLES: {}", pretty_integer(state.debug_state.cpu_cycles));
    println!("MEMORY: {}", pretty_integer(state.memory.0.len()));
    println!();

    let runtime_memory_size = state.memory.0.len() - (PUBLIC_INPUT_START + public_input.len());
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
        (DIMENSION * (state.ap_vec - state.initial_ap_vec)) as f64 / runtime_memory_size as f64 * 100.0
    );
    let used_memory_cells = state.memory
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

    if state.debug_state.poseidon16_calls + state.debug_state.poseidon24_calls > 0 {
        println!(
            "Poseidon2_16 calls: {}, Poseidon2_24 calls: {} (1 poseidon per {} instructions)",
            pretty_integer(state.debug_state.poseidon16_calls),
            pretty_integer(state.debug_state.poseidon24_calls),
            state.debug_state.cpu_cycles / (state.debug_state.poseidon16_calls + state.debug_state.poseidon24_calls)
        );
    }
    if state.debug_state.dot_product_ext_ext_calls > 0 {
        println!(
            "DotProduct calls: {}",
            pretty_integer(state.debug_state.dot_product_ext_ext_calls)
        );
    }
    if state.debug_state.multilinear_eval_calls > 0 {
        println!(
            "MultilinearEval calls: {}",
            pretty_integer(state.debug_state.multilinear_eval_calls)
        );
    }

    if false {
        println!("Low level instruction counts:");
        println!(
            "COMPUTE: {} ({} ADD, {} MUL)",
            state.debug_state.add_counts + state.debug_state.mul_counts,
            state.debug_state.add_counts,
            state.debug_state.mul_counts
        );
        println!("DEREF: {}", state.debug_state.deref_counts);
        println!("JUMP: {}", state.debug_state.jump_counts);
    }

    println!("──────────────────────────────────────────────────────────────────────────\n");
}

fn execute_hints(
    state: &mut State,
    hints: &Vec<Hint>,
    std_out: &mut String,
    instruction_history: &mut ExecutionHistory,
) -> Result<bool, RunnerError> {
    // Hints do not increase state.pc, but they can mutate other parts of the state.
    for hint in hints {
        match hint {
            Hint::RequestMemory {
                offset,
                size,
                vectorized,
                vectorized_len,
            } => {
                let size = size.read_value(&state.memory, state.fp)?.to_usize();
                let pos = state.fp + *offset;

                if *vectorized {
                    assert!(*vectorized_len >= LOG_VECTOR_LEN, "TODO");

                    // padding:
                    while !(state.ap_vec * VECTOR_LEN).is_multiple_of(1 << *vectorized_len) {
                        state.ap_vec += 1;
                    }

                    let val = F::from_usize(state.ap_vec >> (*vectorized_len - LOG_VECTOR_LEN));
                    state.memory.set(state.fp + *offset, val)?;
                    state.ap_vec += size << (*vectorized_len - LOG_VECTOR_LEN);
                } else {
                    state.memory.set(pos, F::from_usize(state.ap))?;
                    state.ap += size;
                }
            }
            Hint::DecomposeBits {
                res_offset,
                to_decompose,
            } => {
                let mut memory_index = state.fp + *res_offset;
                for value_source in to_decompose {
                    let value = value_source.read_value(&state.memory, state.fp)?.to_usize();
                    for i in 0..F::bits() {
                        let bit = F::from_bool(value & (1 << i) != 0);
                        state.memory.set(memory_index, bit)?;
                        memory_index += 1;
                    }
                }
            }
            Hint::CounterHint { res_offset } => {
                let pos = state.fp + *res_offset;
                state.memory.set(pos, F::from_usize(state.debug_state.counter_hint))?;
                state.debug_state.counter_hint += 1;
            }
            Hint::Inverse { arg, res_offset } => {
                let value = arg.read_value(&state.memory, state.fp)?;
                let result = value.try_inverse().unwrap_or(F::ZERO);
                let pos = state.fp + *res_offset;
                state.memory.set(pos, result)?;
            }
            Hint::Print { line_info, content } => {
                let values = content
                    .iter()
                    .map(|value| Ok(value.read_value(&state.memory, state.fp)?.to_string()))
                    .collect::<Result<Vec<_>, _>>()?;
                // Logs for performance analysis:
                if values[0] == "123456789" {
                    if values.len() == 1 {
                        *std_out += "[CHECKPOINT]\n";
                    } else {
                        assert_eq!(values.len(), 2);
                        let new_no_vec_memory = state.ap - state.checkpoint_state.checkpoint_ap;
                        let new_vec_memory = (state.ap_vec - state.checkpoint_state.checkpoint_ap_vec) * DIMENSION;
                        *std_out += &format!(
                            "[CHECKPOINT {}] new CPU cycles: {}, new runtime memory: {} ({:.1}% vec)\n",
                            values[1],
                            pretty_integer(state.debug_state.cpu_cycles - state.checkpoint_state.last_checkpoint_cpu_cycles),
                            pretty_integer(new_no_vec_memory + new_vec_memory),
                            new_vec_memory as f64 / (new_no_vec_memory + new_vec_memory) as f64
                                * 100.0
                        );
                    }

                    state.checkpoint_state.last_checkpoint_cpu_cycles = state.debug_state.cpu_cycles;
                    state.checkpoint_state.checkpoint_ap = state.ap;
                    state.checkpoint_state.checkpoint_ap_vec = state.ap_vec;
                    return Ok(true); // Return early to continue the execution loop
                }

                let line_info = line_info.replace(';', "");
                *std_out += &format!("\"{}\" -> {}\n", line_info, values.join(", "));
            }
            Hint::LocationReport { location } => {
                instruction_history.lines.push(*location);
                instruction_history.cycles.push(state.debug_state.cpu_cycles_before_new_line);
                state.debug_state.cpu_cycles_before_new_line = 0;
            }
            Hint::RangeCheck { value, max } => {
                state.pending_range_checks.insert(state.ap, (value.read_value(&state.memory, state.fp)?.to_usize(), max.read_value(&state.memory, state.fp)?.to_usize()));
            }
        }
    }
    Ok(false) // Don't continue the execution loop
}

fn execute_instruction(
    state: &mut State,
    instruction: &Instruction,
) -> Result<(), RunnerError> {
    match instruction {
        Instruction::Computation {
            operation,
            arg_a,
            arg_c,
            res,
        } => {
            if res.is_value_unknown(&state.memory, state.fp) {
                let memory_address_res = res.memory_address(state.fp)?;
                let a_value = arg_a.read_value(&state.memory, state.fp)?;
                let b_value = arg_c.read_value(&state.memory, state.fp)?;
                let res_value = operation.compute(a_value, b_value);
                state.memory.set(memory_address_res, res_value)?;
            } else if arg_a.is_value_unknown(&state.memory, state.fp) {
                let memory_address_a = arg_a.memory_address(state.fp)?;
                let res_value = res.read_value(&state.memory, state.fp)?;
                let b_value = arg_c.read_value(&state.memory, state.fp)?;
                let a_value = operation
                    .inverse_compute(res_value, b_value)
                    .ok_or(RunnerError::DivByZero)?;
                state.memory.set(memory_address_a, a_value)?;
            } else if arg_c.is_value_unknown(&state.memory, state.fp) {
                let memory_address_b = arg_c.memory_address(state.fp)?;
                let res_value = res.read_value(&state.memory, state.fp)?;
                let a_value = arg_a.read_value(&state.memory, state.fp)?;
                let b_value = operation
                    .inverse_compute(res_value, a_value)
                    .ok_or(RunnerError::DivByZero)?;
                state.memory.set(memory_address_b, b_value)?;
            } else {
                let a_value = arg_a.read_value(&state.memory, state.fp)?;
                let b_value = arg_c.read_value(&state.memory, state.fp)?;
                let res_value = res.read_value(&state.memory, state.fp)?;
                let computed_value = operation.compute(a_value, b_value);
                if res_value != computed_value {
                    return Err(RunnerError::NotEqual(computed_value, res_value));
                }
            }

            match operation {
                Operation::Add => state.debug_state.add_counts += 1,
                Operation::Mul => state.debug_state.mul_counts += 1,
            }

            state.increment_pc();
        }
        Instruction::Deref {
            shift_0,
            shift_1,
            res,
        } => {
            if res.is_value_unknown(&state.memory, state.fp) {
                let pos = res.memory_address(state.fp)?;
                let ptr = state.memory.get(state.fp + shift_0)?;
                let value = state.memory.get(ptr.to_usize() + shift_1)?;
                state.memory.set(pos, value)?;
            } else {
                let value = res.read_value(&state.memory, state.fp)?;
                let ptr = state.memory.get(state.fp + shift_0)?;
                let pos = ptr.to_usize() + shift_1;
                state.memory.set(pos, value)?;
            }

            state.debug_state.deref_counts += 1;
            state.increment_pc();
        }
        Instruction::Jump {
            condition,
            dest,
            updated_fp,
        } => {
            let condition_value = condition.read_value(&state.memory, state.fp)?;
            assert!([F::ZERO, F::ONE].contains(&condition_value),);
            if condition_value == F::ZERO {
                state.increment_pc();
            } else {
                state.pc = dest.read_value(&state.memory, state.fp)?.to_usize();
                state.fp = updated_fp.read_value(&state.memory, state.fp)?.to_usize();
            }

            state.debug_state.jump_counts += 1;
        }
        Instruction::Poseidon2_16 { arg_a, arg_b, res } => {
            state.debug_state.poseidon16_calls += 1;

            let a_value = arg_a.read_value(&state.memory, state.fp)?;
            let b_value = arg_b.read_value(&state.memory, state.fp)?;
            let res_value = res.read_value(&state.memory, state.fp)?;

            let arg0 = state.memory.get_vector(a_value.to_usize())?;
            let arg1 = state.memory.get_vector(b_value.to_usize())?;

            let mut input = [F::ZERO; VECTOR_LEN * 2];
            input[..VECTOR_LEN].copy_from_slice(&arg0);
            input[VECTOR_LEN..].copy_from_slice(&arg1);

            state.precomputed.poseidon_16.permute_mut(&mut input);

            let res0: [F; VECTOR_LEN] = input[..VECTOR_LEN].try_into().unwrap();
            let res1: [F; VECTOR_LEN] = input[VECTOR_LEN..].try_into().unwrap();

            state.memory.set_vector(res_value.to_usize(), res0)?;
            state.memory.set_vector(1 + res_value.to_usize(), res1)?;

            state.increment_pc();
        }
        Instruction::Poseidon2_24 { arg_a, arg_b, res } => {
            state.debug_state.poseidon24_calls += 1;

            let a_value = arg_a.read_value(&state.memory, state.fp)?;
            let b_value = arg_b.read_value(&state.memory, state.fp)?;
            let res_value = res.read_value(&state.memory, state.fp)?;

            let arg0 = state.memory.get_vector(a_value.to_usize())?;
            let arg1 = state.memory.get_vector(1 + a_value.to_usize())?;
            let arg2 = state.memory.get_vector(b_value.to_usize())?;

            let mut input = [F::ZERO; VECTOR_LEN * 3];
            input[..VECTOR_LEN].copy_from_slice(&arg0);
            input[VECTOR_LEN..2 * VECTOR_LEN].copy_from_slice(&arg1);
            input[2 * VECTOR_LEN..].copy_from_slice(&arg2);

            state.precomputed.poseidon_24.permute_mut(&mut input);

            let res: [F; VECTOR_LEN] = input[2 * VECTOR_LEN..].try_into().unwrap();

            state.memory.set_vector(res_value.to_usize(), res)?;

            state.increment_pc();
        }
        Instruction::DotProductExtensionExtension {
            arg0,
            arg1,
            res,
            size,
        } => {
            state.debug_state.dot_product_ext_ext_calls += 1;

            let ptr_arg_0 = arg0.read_value(&state.memory, state.fp)?.to_usize();
            let ptr_arg_1 = arg1.read_value(&state.memory, state.fp)?.to_usize();
            let ptr_res = res.read_value(&state.memory, state.fp)?.to_usize();

            let slice_0 = state.memory.get_continuous_slice_of_ef_elements(ptr_arg_0, *size)?;
            let slice_1 = state.memory.get_continuous_slice_of_ef_elements(ptr_arg_1, *size)?;

            let dot_product = dot_product::<EF, _, _>(slice_0.into_iter(), slice_1.into_iter());
            state.memory.set_ef_element(ptr_res, dot_product)?;

            state.increment_pc();
        }
        Instruction::MultilinearEval {
            coeffs,
            point,
            res,
            n_vars,
        } => {
            state.debug_state.multilinear_eval_calls += 1;

            let ptr_coeffs = coeffs.read_value(&state.memory, state.fp)?.to_usize();
            let ptr_point = point.read_value(&state.memory, state.fp)?.to_usize();
            let ptr_res = res.read_value(&state.memory, state.fp)?.to_usize();
            let n_coeffs = 1 << *n_vars;
            let slice_coeffs = state.memory.slice(ptr_coeffs << *n_vars, n_coeffs)?;

            let log_point_size = log2_ceil_usize(*n_vars * DIMENSION);
            let point_slice = state.memory.slice(ptr_point << log_point_size, *n_vars * DIMENSION)?;
            for i in *n_vars * DIMENSION..(*n_vars * DIMENSION).next_power_of_two() {
                let pos = (ptr_point << log_point_size) + i;
                state.memory.set(pos, F::ZERO)?; // padding
            }
            let point = point_slice[..*n_vars * DIMENSION]
                .chunks_exact(DIMENSION)
                .map(|chunk| EF::from_basis_coefficients_slice(chunk).unwrap())
                .collect::<Vec<_>>();

            let eval = slice_coeffs.evaluate(&MultilinearPoint(point));
            let mut res_vec = eval.as_basis_coefficients_slice().to_vec();
            res_vec.resize(VECTOR_LEN, F::ZERO);
            state.memory.set_vector(ptr_res, res_vec.clone().try_into().unwrap())?;

            state.increment_pc();
        }
    }
    Ok(())
}

struct State {
    memory: Memory,
    bytecode: Bytecode,
    public_memory_size: usize,
    pc: usize,
    fp: usize,
    ap: usize,
    initial_ap: usize,
    initial_ap_vec: usize,
    ap_vec: usize,
    precomputed: Precomputed,
    debug_state: DebugState,
    checkpoint_state: CheckpointState,
    pending_range_checks: BTreeMap<usize, (usize, usize)>,
}

struct Precomputed {
    poseidon_16: Poseidon16,
    poseidon_24: Poseidon24,
}

struct DebugState {
    poseidon16_calls: usize,
    poseidon24_calls: usize,
    dot_product_ext_ext_calls: usize,
    multilinear_eval_calls: usize,
    cpu_cycles: usize,
    add_counts: usize,
    mul_counts: usize,
    deref_counts: usize,
    jump_counts: usize,
    counter_hint: usize,
    cpu_cycles_before_new_line: usize,
    pcs: Vec<usize>,
    fps: Vec<usize>,
}

struct CheckpointState {
    checkpoint_ap: usize,
    checkpoint_ap_vec: usize,
    last_checkpoint_cpu_cycles: usize,
}

impl DebugState {
    fn init() -> DebugState {
        DebugState {
            poseidon16_calls: 0,
            poseidon24_calls: 0,
            dot_product_ext_ext_calls: 0,
            multilinear_eval_calls: 0,
            cpu_cycles: 0,
            add_counts: 0,
            mul_counts: 0,
            deref_counts: 0,
            jump_counts: 0,
            counter_hint: 0,
            cpu_cycles_before_new_line: 0,
            pcs: Vec::new(),
            fps: Vec::new(),
        }
    }
}

impl CheckpointState {
    fn init(
        initial_ap: usize,
        initial_ap_vec: usize,
    ) -> CheckpointState {
        CheckpointState {
            last_checkpoint_cpu_cycles: 0,
            checkpoint_ap: initial_ap,
            checkpoint_ap_vec: initial_ap_vec,
        }
    }
}

impl State {
    fn init(
        bytecode: &Bytecode,
        public_input: &[F],
        private_input: &[F],
        no_vec_runtime_memory: usize,
    ) -> Result<State, RunnerError> {
        let mut memory = Memory::new(build_public_memory(public_input));
        let public_memory_size = (PUBLIC_INPUT_START + public_input.len()).next_power_of_two();
        let mut fp = public_memory_size;

        for (i, value) in private_input.iter().enumerate() {
            memory.set(fp + i, *value)?;
        }

        fp += private_input.len();
        fp = fp.next_multiple_of(DIMENSION);

        let initial_ap = fp + bytecode.starting_frame_memory;
        let initial_ap_vec =
            (initial_ap + no_vec_runtime_memory).next_multiple_of(VECTOR_LEN) / VECTOR_LEN;

        Ok(State {
            memory,
            bytecode: bytecode.clone(),
            public_memory_size,
            pc: 0,
            fp: fp,
            initial_ap,
            initial_ap_vec,
            ap: initial_ap,
            ap_vec: initial_ap_vec,
            pending_range_checks: BTreeMap::new(),
            precomputed: Precomputed {
                poseidon_16: get_poseidon16().clone(),
                poseidon_24: get_poseidon24().clone(),
            },
            debug_state: DebugState::init(),
            checkpoint_state: CheckpointState::init(initial_ap, initial_ap_vec),
        })
    }

    fn increment_pc(&mut self) {
        self.pc += 1;
    }
}
