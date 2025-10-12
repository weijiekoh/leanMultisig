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

fn find_next_zero_cell(state: &State, start_offset: usize) -> usize {
    // TODO: fix this there may not be a zero cell to locate and this function may run forever!
    let mut z = start_offset;
    loop { 
        let m_fp_z = &state.memory.get(state.fp + z);
        if !m_fp_z.is_err() && m_fp_z.clone().unwrap() == F::ZERO {
            break;
        }
        z += 1;
    }
    z
}

fn find_next_undefined_cell(state: &State, start_offset: usize) -> usize {
    let mut z = start_offset;
    loop { 
        if matches!(&state.memory.get(state.fp + z), Err(RunnerError::UndefinedMemory)) {
            break;
        }
        z += 1;
    }
    z
}

fn find_next_undefined_cell_from_mem(
    mem: &Memory,
    conflicts: &BTreeSet<usize>,
    memory_write_history: &BTreeMap<usize, (usize, usize)>,
    pos: usize,
) -> usize {
    let mut z = pos;

    while !matches!(mem.get(z), Err(RunnerError::UndefinedMemory)) {
        z += 1;
    }

    loop {
        if conflicts.contains(&z) || memory_write_history.contains_key(&z) {
            z = find_next_undefined_cell_from_mem(mem, conflicts, memory_write_history, z + 1);
        } else {
            break;
        }
    }
    z
}

pub fn calc_t_1_v(v: usize, t: usize) -> usize {
    (F::from_usize(v) - F::ONE - F::from_usize(t)).to_usize()
}

pub fn is_undef(mem: &Memory, pos: usize) -> bool {
    matches!(mem.get(pos), Err(RunnerError::UndefinedMemory))
}

pub fn compile_range_checks(
    first_exec: &ExecutionResult,
    bytecode: &Bytecode,
) -> Result<Bytecode, RunnerError> {
    /*
     * With val stored in m[fp + x], and t being a constant, the goal is to replace each RangeCheck
     * instruction with the following 3 instructions:
     *
     * 1. Using DEREF, set `m[fp + i]` to `m[m[fp + x]]`.
     *     - Since this will fail if `m[fp + x] >= M`, we ensure that `m[fp + x] < M`.
     * 
     * 2. Using ADD, ensure (via constraint-solving): `m[fp + j] + m[m[fp + x]] = (t - 1)`.
     * 
     * 3. Using DEREF, ensure `m[m[fp + j]] = m[fp + k]`.
     *     - Since this will fail if `m[fp + j] >= M`, we ensure that `(t - 1) - m[fp + x] < M`.
     *
     * according to section 2.5.3 of minimal_zkVM.pdf.
     *
     * This is how we solve for the i, j, and k values. First, establish these principles:
     *
     * 1. Performing a DEREF of the form m[m[fp + x]] == m[fp + i] will fail if:
     *      - both m[m[fp + x]] and m[fp + i] are undefined
     *      - m[m[fp + x]] is defined, and m[fp + i] is already set to a different value
     *      - m[fp + i] is defined, and m[m[fp + x]] is already set to a different value
     * 2. Performing a DEREF of the form m[m[fp + x]] == m[fp + i] will succeed if:
     *      - m[m[fp + x]] is defined, and m[fp + i] is undefined
     *      - m[fp + i] is defined, and m[m[fp + x]] is undefined
     * 3. Performing and ADD of the form m[fp + j] + m[m[fp + x]] == c will fail if:
     *      - both m[fp + j] and m[m[fp + x]] are undefined
     * 4. Performing and ADD of the form m[fp + j] + m[m[fp + x]] == c will succeed if:
     *      - m[fp + j] is undefined
     *
     * Most importantly, at each range check, we need to know if m[m[fp + x]] or m[m[fp + j]] will
     * be set at some point in the future, and if so, what it will be set to, or if it will have
     * already been set. This can be done by looking up the memory_write_history map in first_exec.
     * We also need to consider if the memory location was set during initialisation.
     *
     * TODO: rewrite this
     */

    // Convenience mapping: instr_idx -> (fp, offset, val, t, t - 1 - v)
    let mut rcs: BTreeMap<usize, (usize, usize, usize, usize, usize)> = BTreeMap::new();

    // Stores the keys of rcs in order of execution
    let mut rcs_idxs: Vec<usize> = Vec::with_capacity(rcs.len());

    // Used for the first instruction to set the zero cell
    let mut first_rcs_fp = None;

    for i in 0..bytecode.instructions.len() {
        match &bytecode.instructions[i] {
            Instruction::RangeCheck { value, max } => {
                // Find the execution step where this instruction was executed
                let execution_step = first_exec.pcs.iter().position(|&pc| pc == i);
                if let Some(step) = execution_step {
                    let fp = first_exec.fps[step];
                    if first_rcs_fp.is_none() {
                        first_rcs_fp = Some(fp);
                    }
                    
                    // Get the offset of the value from the current fp
                    let v_off = match value {
                        MemOrFp::MemoryAfterFp { offset } => *offset,
                        MemOrFp::Fp => 0, // fp is at offset 0
                    };
                    
                    // Get v and t
                    let v = first_exec.memory.get(fp + v_off).unwrap().to_usize();
                    let t = match max {
                        MemOrConstant::Constant(t) => t.to_usize(),
                        MemOrConstant::MemoryAfterFp { .. } => unimplemented!(),
                    };

                    // Update the convenience mapping
                    rcs.insert(i, (fp, v_off, v, t, calc_t_1_v(t, v)));
                    rcs_idxs.push(i);
                }
            }
            _ => {}
        }
    }

    // Return the bytecode unmodified if there are no range checks
    if rcs.is_empty() {
        return Ok(bytecode.clone());
    }

    // Create the grid. Some(index) = defined at said instr index, None = undefined
    let mut v_pos: BTreeMap<usize, Option<(i32, usize)>> = BTreeMap::new();
    let mut q_pos: BTreeMap<usize, Option<(i32, usize)>> = BTreeMap::new();

    // The set of memory locations that may conflict with auxillary cells
    let mut conflicts: BTreeSet<usize> = BTreeSet::new();

    fn lookup_initial_memory(value: usize, initial_memory: &Memory) -> Option<usize> {
        for i in 0..initial_memory.0.len() {
            if initial_memory.0[i].is_some() && initial_memory.0[i].unwrap().to_usize() == value {
                return Some(i);
            }
        }
        None
    }

    // Populate the v and q rows, as well as conflicts
    for i in &rcs_idxs {
        let (_fp, _v_off, v, _t, q) = rcs.get(&i).unwrap();

        // Check if v and q are already defined in first_exec.memory_write_history or
        // first_exec.initial_memory

        // If v < initial_memory.len(), then assume it's defined
        if *v >= first_exec.initial_memory.0.len() {
            let vv = first_exec.memory_write_history.get(&v).copied();
            if vv.is_some() {
                let vu = vv.unwrap();
                v_pos.insert(*i, Some((vu.0 as i32, vu.1)));
            } else {
                v_pos.insert(*i, None);
            }
        } else {
            let cell = first_exec.initial_memory.get(*v).unwrap().to_usize();
            v_pos.insert(*i, Some((-1, cell)));
        }

        // If q < initial_memory.len(), then assume it's defined
        if *q >= first_exec.initial_memory.0.len() {
            let qq = first_exec.memory_write_history.get(&q).copied();
            if qq.is_some() {
                let qu = qq.unwrap();
                q_pos.insert(*i, Some((qu.0 as i32, qu.1)));
            } else {
                q_pos.insert(*i, None);
            }
        } else {
            let cell = first_exec.initial_memory.get(*q).unwrap().to_usize();
            q_pos.insert(*i, Some((-1, cell)));
        }
        conflicts.insert(*v);
        conflicts.insert(*q);
    }

    // Used to find an undefined cell to set it to 0 such that it can be accessed by DEREF by any
    // DEREF in the code, no matter where it is
    let largest_fp = first_exec.fps.iter().max().unwrap();
    let z_pos = find_next_undefined_cell_from_mem(
        &first_exec.memory,
        &conflicts,
        &first_exec.memory_write_history,
        *largest_fp,
    );
    conflicts.insert(z_pos);

    let z_instr = Instruction::Computation {
        operation: Operation::Add,
        arg_a: MemOrConstant::Constant(F::ZERO),
        arg_c: MemOrFp::MemoryAfterFp { offset: z_pos - first_rcs_fp.unwrap() },
        res: MemOrConstant::Constant(F::ZERO),
    };

    let mut instrs_to_insert: BTreeMap<usize, Vec<Instruction>> = BTreeMap::new();
    for i in 0..rcs.len() {
        instrs_to_insert.insert(rcs_idxs[i], vec![]);
    }

    instrs_to_insert.get_mut(&rcs_idxs[0]).unwrap().push(z_instr);
    println!("z_pos: {}", z_pos);
    println!("rcs: {:?}", rcs);

    for i in &rcs_idxs {
        let (fp, v_off, _v, _t, q) = rcs.get(&i).unwrap();

        // Step 1: deref m[m[fp + x]] == m[fp + i]
        let step_1 = match v_pos.get(i).unwrap() {
            Some((instr_pc, cell)) => {
                if *instr_pc > *i as i32 {
                    // m[v] will be defined later, so set it to that value
                    Instruction::Deref {
                        shift_0: *v_off,
                        shift_1: 0,
                        res: MemOrFpOrConstant::Constant(F::from_usize(*cell)),
                    }
                } else {
                    // m[v] has been defined, so search for an i where m[fp + i] is undefined
                    let abs_pos = find_next_undefined_cell_from_mem(
                        &first_exec.memory,
                        &conflicts,
                        &first_exec.memory_write_history,
                        *fp + 1,
                    );

                    conflicts.insert(abs_pos);
                    println!("setting m[{}] to m[m[fp + {}] + 0]", abs_pos, v_off);

                    Instruction::Deref {
                        shift_0: *v_off,
                        shift_1: 0,
                        res: MemOrFpOrConstant::MemoryAfterFp { offset: abs_pos - fp },
                    }
                }
            }
            None => {
                // m[v] will be undefined, so use z
                Instruction::Deref {
                    shift_0: *v_off,
                    shift_1: 0,
                    res: MemOrFpOrConstant::MemoryAfterFp { offset: z_pos - fp },
                }
            }
        };

        // Step 2: m[fp + j] = t - 1 - v
        let abs_j_pos = find_next_undefined_cell_from_mem(
            &first_exec.memory,
            &conflicts,
            &first_exec.memory_write_history,
            *fp,
        );

        conflicts.insert(abs_j_pos);

        let step_2 = Instruction::Computation {
            operation: Operation::Add,
            arg_a: MemOrConstant::Constant(F::ZERO), // 0
            arg_c: MemOrFp::MemoryAfterFp { offset: abs_j_pos - fp }, // Unknown; solves to t - 1 - v
            res: MemOrConstant::Constant(F::from_usize(*q)), // t - 1 - v
        };

        // Step 3: m[fp + k] = m[m[fp + j]]
        let step_3 = match q_pos.get(i).unwrap() {
            Some((instr_pc, cell)) => {
                if *instr_pc > *i as i32 {
                    // m[q] will be defined later, so set it to that value
                    Instruction::Deref {
                        shift_0: abs_j_pos - fp,
                        shift_1: 0,
                        res: MemOrFpOrConstant::Constant(F::from_usize(*cell)),
                    }
                } else {
                    // m[q] has been defined, so search for an k where m[fp + k] is undefined
                    let abs_k_pos = find_next_undefined_cell_from_mem(
                        &first_exec.memory,
                        &conflicts,
                        &first_exec.memory_write_history,
                        *fp,
                    );
                    conflicts.insert(abs_k_pos);
                    Instruction::Deref {
                        shift_0: abs_j_pos - fp,
                        shift_1: 0,
                        res: MemOrFpOrConstant::MemoryAfterFp { offset: abs_k_pos - fp },
                    }
                }
            }
            None => {
                println!("3");
                // If m[q] will not be defined, so use z
                Instruction::Deref {
                    shift_0: abs_j_pos - fp,
                    shift_1: 0,
                    res: MemOrFpOrConstant::MemoryAfterFp { offset: z_pos - fp },
                }
            }
        };

        instrs_to_insert.get_mut(i).unwrap().push(step_1);
        instrs_to_insert.get_mut(i).unwrap().push(step_2);
        instrs_to_insert.get_mut(i).unwrap().push(step_3);
    }

    let mut updated_bytecode = bytecode.clone();
    // Naively replace each range_check with their corresponding steps in instrs_to_insert
    // in-place. Update jump instructions to account for instruction position changes.
    // A next iteration of this should handle the offsets at the compiler level.
    
    let mut new_instructions = Vec::new();
    let mut index_offset = 0; // Tracks how many extra instructions have been inserted so far
    
    for (original_idx, instruction) in bytecode.instructions.iter().enumerate() {
        match instruction {
            Instruction::RangeCheck { .. } => {
                // Replace with generated instruction sequence
                if let Some(replacement_instrs) = instrs_to_insert.get(&original_idx) {
                    new_instructions.extend(replacement_instrs.iter().cloned());
                    // Track the net change in instruction count
                    index_offset += replacement_instrs.len().saturating_sub(1);
                } else {
                    // This shouldn't happen since we populated instrs_to_insert for all range checks
                    new_instructions.push(instruction.clone());
                }
            }
            Instruction::Jump { condition, dest, updated_fp } => {
                // Update jump destinations to account for inserted instructions
                let updated_dest = match dest {
                    MemOrConstant::Constant(old_dest_field) => {
                        let old_dest = old_dest_field.to_usize();
                        // Calculate how many instructions were inserted before this jump destination
                        let offset_at_dest = instrs_to_insert.iter()
                            .filter(|(idx, _instrs)| **idx < old_dest)
                            .map(|(_, instrs)| instrs.len().saturating_sub(1))
                            .sum::<usize>();
                        let new_dest = old_dest + offset_at_dest;
                        MemOrConstant::Constant(F::from_usize(new_dest))
                    }
                    _ => *dest, // Don't modify non-constant destinations
                };
                
                new_instructions.push(Instruction::Jump {
                    condition: *condition,
                    dest: updated_dest,
                    updated_fp: *updated_fp,
                });
            }
            _ => {
                // Copy other instructions unchanged
                new_instructions.push(instruction.clone());
            }
        }
    }

    // Update the instructions
    updated_bytecode.instructions = new_instructions;

    // Adjust ending_pc for inserted instructions
    updated_bytecode.ending_pc = bytecode.ending_pc + index_offset; 
    
    // Update hints to account for shifted instruction positions
    let mut updated_hints = BTreeMap::new();
    for (pc, hints) in &bytecode.hints {
        let offset_at_pc = instrs_to_insert.iter()
            .filter(|(idx, _instrs)| **idx < *pc)
            .map(|(_, instrs)| instrs.len().saturating_sub(1))
            .sum::<usize>();
        updated_hints.insert(pc + offset_at_pc, hints.clone());
    }
    updated_bytecode.hints = updated_hints;

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
    pub memory_write_history: BTreeMap<usize, (usize, usize)>,
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

#[allow(clippy::too_many_arguments)] // TODO
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

    // address -> (pc, value) at which it was first written
    let mut memory_write_history: BTreeMap<usize, (usize, usize)> = BTreeMap::new();
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
            &mut memory_write_history,
        )?;
        
        if should_continue {
            continue;
        }

        let instruction = &bytecode.instructions[state.pc];
        println!("fp: {}; exec pc: {}; instr: {}", state.fp, state.pc, instruction);
        if hints.len() > 0 {
            println!("hints: {:?}", hints);
        }
        execute_instruction(&mut state, &mut memory_write_history, instruction)?;
    }

    debug_assert_eq!(state.pc, bytecode.ending_pc);
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
        memory_write_history,
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
    memory_write_history: &mut BTreeMap<usize, (usize, usize)>,
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
                    memory_write_history.insert(pos, (state.pc, val.to_usize()));
                    state.ap_vec += size << (*vectorized_len - LOG_VECTOR_LEN);
                } else {
                    state.memory.set(pos, F::from_usize(state.ap))?;
                    memory_write_history.insert(pos, (state.pc, state.ap));
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
                        memory_write_history.insert(memory_index, (state.pc, bit.to_usize()));
                        memory_index += 1;
                    }
                }
            }
            Hint::CounterHint { res_offset } => {
                let pos = state.fp + *res_offset;
                state.memory.set(pos, F::from_usize(state.debug_state.counter_hint))?;
                memory_write_history.insert(pos, (state.pc, state.debug_state.counter_hint));
                state.debug_state.counter_hint += 1;
            }
            Hint::Inverse { arg, res_offset } => {
                let value = arg.read_value(&state.memory, state.fp)?;
                let result = value.try_inverse().unwrap_or(F::ZERO);
                let pos = state.fp + *res_offset;
                state.memory.set(pos, result)?;
                memory_write_history.insert(pos, (state.pc, result.to_usize()));
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
        }
    }
    Ok(false) // Don't continue the execution loop
}

fn execute_instruction(
    state: &mut State,
    memory_write_history: &mut BTreeMap<usize, (usize, usize)>,
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
                memory_write_history.insert(memory_address_res, (state.pc, res_value.to_usize()));
            } else if arg_a.is_value_unknown(&state.memory, state.fp) {
                let memory_address_a = arg_a.memory_address(state.fp)?;
                let res_value = res.read_value(&state.memory, state.fp)?;
                let b_value = arg_c.read_value(&state.memory, state.fp)?;
                let a_value = operation
                    .inverse_compute(res_value, b_value)
                    .ok_or(RunnerError::DivByZero)?;
                state.memory.set(memory_address_a, a_value)?;
                memory_write_history.insert(memory_address_a, (state.pc, a_value.to_usize()));
            } else if arg_c.is_value_unknown(&state.memory, state.fp) {
                let memory_address_b = arg_c.memory_address(state.fp)?;
                let res_value = res.read_value(&state.memory, state.fp)?;
                let a_value = arg_a.read_value(&state.memory, state.fp)?;
                let b_value = operation
                    .inverse_compute(res_value, a_value)
                    .ok_or(RunnerError::DivByZero)?;
                state.memory.set(memory_address_b, b_value)?;
                memory_write_history.insert(memory_address_b, (state.pc, b_value.to_usize()));
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
                memory_write_history.insert(pos, (state.pc, value.to_usize()));
            } else {
                let value = res.read_value(&state.memory, state.fp)?;
                let ptr = state.memory.get(state.fp + shift_0)?;
                let pos = ptr.to_usize() + shift_1;
                state.memory.set(pos, value)?;
                memory_write_history.insert(pos, (state.pc, value.to_usize()));
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
        // The second execution should not contain any range checks
        // because after the first execution, which figures out which aux values to set,
        // the runner will replace Instruction::RangeCheck instances with the actual 3-step
        // range check instructions (deref, add, and deref)
        Instruction::RangeCheck { .. } => {
            state.increment_pc();
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
            for (_i, v) in res0.iter().enumerate() {
                memory_write_history.insert(res_value.to_usize(), (state.pc, v.to_usize()));
            }

            state.memory.set_vector(1 + res_value.to_usize(), res1)?;
            for (_i, v) in res1.iter().enumerate() {
                memory_write_history.insert(res_value.to_usize(), (state.pc, v.to_usize()));
            }

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
            for (_i, v) in res.iter().enumerate() {
                memory_write_history.insert(res_value.to_usize(), (state.pc, v.to_usize()));
            }

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

            //for (i, v) in dot_product.as_basis_coefficients_slice().iter().enumerate() {
                //memory_write_history.insert(ptr_res + i, (state.pc, v.to_usize()));
            //}

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
                memory_write_history.insert(pos, (state.pc, 0));
            }
            let point = point_slice[..*n_vars * DIMENSION]
                .chunks_exact(DIMENSION)
                .map(|chunk| EF::from_basis_coefficients_slice(chunk).unwrap())
                .collect::<Vec<_>>();

            let eval = slice_coeffs.evaluate(&MultilinearPoint(point));
            let mut res_vec = eval.as_basis_coefficients_slice().to_vec();
            res_vec.resize(VECTOR_LEN, F::ZERO);
            state.memory.set_vector(ptr_res, res_vec.clone().try_into().unwrap())?;

            for (i, v) in res_vec.iter().enumerate() {
                let idx = VECTOR_LEN * ptr_res + i;
                memory_write_history.insert(idx, (state.pc, v.to_usize()));
            }

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
