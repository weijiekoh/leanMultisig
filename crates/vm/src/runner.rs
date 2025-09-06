use std::collections::BTreeMap;
use std::collections::VecDeque;

use colored::Colorize;
use p3_field::BasedVectorSpace;
use p3_field::PrimeCharacteristicRing;
use p3_field::dot_product;
use rayon::prelude::*;
use utils::ToUsize;
use utils::get_poseidon16;
use utils::get_poseidon24;
use utils::pretty_integer;
use whir_p3::poly::evals::EvaluationsList;
use whir_p3::poly::multilinear::MultilinearPoint;

use crate::bytecode::*;
use crate::*;
use p3_field::Field;
use p3_symmetric::Permutation;

const MAX_MEMORY_SIZE: usize = 1 << 24;
const STACK_TRACE_INSTRUCTIONS: usize = 5000;
const STACK_TRACE_MAX_LINES_PER_FUNCTION: usize = 5;

#[derive(Debug, Clone)]
pub enum RunnerError {
    OutOfMemory,
    MemoryAlreadySet,
    NotAPointer,
    DivByZero,
    NotEqual(F, F),
    UndefinedMemory,
    PCOutOfBounds,
    MultilinearEvalPointNotPadded,
}

impl ToString for RunnerError {
    fn to_string(&self) -> String {
        match self {
            RunnerError::OutOfMemory => "Out of memory".to_string(),
            RunnerError::MemoryAlreadySet => "Memory already set".to_string(),
            RunnerError::NotAPointer => "Not a pointer".to_string(),
            RunnerError::DivByZero => "Division by zero".to_string(),
            RunnerError::NotEqual(expected, actual) => {
                format!("Computation Invalid: {} != {}", expected, actual)
            }
            RunnerError::UndefinedMemory => "Undefined memory access".to_string(),
            RunnerError::PCOutOfBounds => "Program counter out of bounds".to_string(),
            RunnerError::MultilinearEvalPointNotPadded => {
                "Point for multilinear eval not padded with zeros".to_string()
            }
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct Memory(pub Vec<Option<F>>);

impl MemOrConstant {
    pub fn read_value(&self, memory: &Memory, fp: usize) -> Result<F, RunnerError> {
        match self {
            MemOrConstant::Constant(c) => Ok(*c),
            MemOrConstant::MemoryAfterFp { offset } => memory.get(fp + *offset),
        }
    }

    pub fn is_value_unknown(&self, memory: &Memory, fp: usize) -> bool {
        self.read_value(memory, fp).is_err()
    }

    pub fn memory_address(&self, fp: usize) -> Result<usize, RunnerError> {
        match self {
            MemOrConstant::Constant(_) => Err(RunnerError::NotAPointer),
            MemOrConstant::MemoryAfterFp { offset } => Ok(fp + *offset),
        }
    }
}

impl MemOrFp {
    pub fn read_value(&self, memory: &Memory, fp: usize) -> Result<F, RunnerError> {
        match self {
            MemOrFp::MemoryAfterFp { offset } => memory.get(fp + *offset),
            MemOrFp::Fp => Ok(F::from_usize(fp)),
        }
    }

    pub fn is_value_unknown(&self, memory: &Memory, fp: usize) -> bool {
        self.read_value(memory, fp).is_err()
    }

    pub fn memory_address(&self, fp: usize) -> Result<usize, RunnerError> {
        match self {
            MemOrFp::MemoryAfterFp { offset } => Ok(fp + *offset),
            MemOrFp::Fp => Err(RunnerError::NotAPointer),
        }
    }
}

impl MemOrFpOrConstant {
    pub fn read_value(&self, memory: &Memory, fp: usize) -> Result<F, RunnerError> {
        match self {
            MemOrFpOrConstant::MemoryAfterFp { offset } => memory.get(fp + *offset),
            MemOrFpOrConstant::Fp => Ok(F::from_usize(fp)),
            MemOrFpOrConstant::Constant(c) => Ok(*c),
        }
    }

    pub fn is_value_unknown(&self, memory: &Memory, fp: usize) -> bool {
        self.read_value(memory, fp).is_err()
    }

    pub fn memory_address(&self, fp: usize) -> Result<usize, RunnerError> {
        match self {
            MemOrFpOrConstant::MemoryAfterFp { offset } => Ok(fp + *offset),
            MemOrFpOrConstant::Fp => Err(RunnerError::NotAPointer),
            MemOrFpOrConstant::Constant(_) => Err(RunnerError::NotAPointer),
        }
    }
}

impl Memory {
    pub fn new(public_memory: Vec<F>) -> Self {
        Self(public_memory.into_par_iter().map(Some).collect::<Vec<_>>())
    }
    pub fn get(&self, index: usize) -> Result<F, RunnerError> {
        self.0
            .get(index)
            .and_then(|opt| *opt)
            .ok_or(RunnerError::UndefinedMemory)
    }

    pub fn set(&mut self, index: usize, value: F) -> Result<(), RunnerError> {
        if index >= self.0.len() {
            if index >= MAX_MEMORY_SIZE {
                return Err(RunnerError::OutOfMemory);
            }
            self.0.resize(index + 1, None);
        }
        if let Some(existing) = &mut self.0[index] {
            if *existing != value {
                return Err(RunnerError::MemoryAlreadySet);
            }
        } else {
            self.0[index] = Some(value);
        }
        Ok(())
    }

    pub fn get_vector(&self, index: usize) -> Result<[F; VECTOR_LEN], RunnerError> {
        Ok(self.get_vectorized_slice(index, 1)?.try_into().unwrap())
    }

    pub fn get_ef_element(&self, index: usize) -> Result<EF, RunnerError> {
        // index: non vectorized pointer
        let mut coeffs = [F::ZERO; DIMENSION];
        for i in 0..DIMENSION {
            coeffs[i] = self.get(index + i)?;
        }
        Ok(EF::from_basis_coefficients_slice(&coeffs).unwrap())
    }

    pub fn get_vectorized_slice(&self, index: usize, len: usize) -> Result<Vec<F>, RunnerError> {
        let mut vector = Vec::with_capacity(len * VECTOR_LEN);
        for i in 0..len * VECTOR_LEN {
            vector.push(self.get(index * VECTOR_LEN + i)?);
        }
        Ok(vector)
    }

    pub fn get_continuous_slice_of_ef_elements(
        &self,
        index: usize, // normal pointer
        len: usize,
    ) -> Result<Vec<EF>, RunnerError> {
        let mut vector = Vec::with_capacity(len);
        for i in 0..len {
            vector.push(self.get_ef_element(index + i * DIMENSION)?);
        }
        Ok(vector)
    }

    pub fn slice(&self, index: usize, len: usize) -> Result<Vec<F>, RunnerError> {
        let mut vector = Vec::with_capacity(len);
        for i in 0..len {
            vector.push(self.get(index + i)?);
        }
        Ok(vector)
    }

    pub fn set_ef_element(&mut self, index: usize, value: EF) -> Result<(), RunnerError> {
        for (i, v) in value.as_basis_coefficients_slice().iter().enumerate() {
            self.set(index + i, *v)?;
        }
        Ok(())
    }

    pub fn set_vector(&mut self, index: usize, value: [F; VECTOR_LEN]) -> Result<(), RunnerError> {
        for (i, v) in value.iter().enumerate() {
            let idx = VECTOR_LEN * index + i;
            self.set(idx, *v)?;
        }
        Ok(())
    }

    pub fn set_vectorized_slice(&mut self, index: usize, value: &[F]) -> Result<(), RunnerError> {
        assert!(value.len() % VECTOR_LEN == 0);
        for (i, v) in value.iter().enumerate() {
            let idx = VECTOR_LEN * index + i;
            self.set(idx, *v)?;
        }
        Ok(())
    }
}

fn pretty_stack_trace(
    source_code: &str,
    latest_instructions: &VecDeque<LocationInSourceCode>,
    function_locations: &BTreeMap<usize, String>,
) -> String {
    let source_lines: Vec<&str> = source_code.lines().collect();
    let mut result = String::new();
    let mut call_stack: Vec<(usize, String)> = Vec::new(); // (line_number, function_name)
    let mut prev_function: Option<String> = None;
    let mut skipped_lines: usize = 0; // Track skipped lines for current function

    result.push_str("╔══════════════════════════════════════════════════════════════╗\n");
    result.push_str("║                       STACK TRACE                            ║\n");
    result.push_str("╚══════════════════════════════════════════════════════════════╝\n\n");

    for (idx, &line_num) in latest_instructions.iter().enumerate() {
        // Find which function this line belongs to
        let current_function = find_function_for_line(line_num, function_locations);

        // Detect function changes
        match (&prev_function, &current_function) {
            (None, Some(func)) => {
                // Initial function entry
                call_stack.push((line_num, func.clone()));
                result.push_str(&format!("┌─ {} (line {})\n", func, line_num));
                skipped_lines = 0;
            }
            (Some(prev), Some(curr)) if prev != curr => {
                // Show skipped lines message if any were skipped
                if skipped_lines > 0 {
                    let indent = "│ ".repeat(call_stack.len());
                    result.push_str(&format!(
                        "{}├─ ... ({} lines skipped) ...\n",
                        indent, skipped_lines
                    ));
                }

                // Check if we're returning to a previous function or calling a new one
                if let Some(pos) = call_stack.iter().position(|(_, f)| f == curr) {
                    // Returning to a previous function - pop the stack
                    while call_stack.len() > pos + 1 {
                        call_stack.pop();
                        let indent = "│ ".repeat(call_stack.len());
                        result.push_str(&format!("{}└─ [return]\n", indent));
                    }
                    skipped_lines = 0;
                } else {
                    // Calling a new function
                    let indent = "│ ".repeat(call_stack.len());

                    // Show the calling instruction
                    if idx > 0 {
                        let caller_line = latest_instructions[idx - 1];
                        let code_line = source_lines
                            .get(caller_line.saturating_sub(1))
                            .unwrap_or(&"<line not found>")
                            .trim();
                        result.push_str(&format!(
                            "{}├─ line {}: {}\n",
                            indent, caller_line, code_line
                        ));
                    }

                    // Add the new function to the stack
                    call_stack.push((line_num, curr.clone()));
                    let indent = "│ ".repeat(call_stack.len() - 1);
                    result.push_str(&format!("{}├─ {} (line {})\n", indent, curr, line_num));
                    skipped_lines = 0;
                }
            }
            _ => {
                // Same function, continue
            }
        }

        // Display the current instruction
        if current_function.is_some() {
            // Determine if we should show this line
            let should_show = if idx == latest_instructions.len() - 1 {
                // Always show the last line (error location)
                true
            } else {
                // Count remaining lines in this function
                let remaining_in_function = count_remaining_lines_in_function(
                    idx,
                    latest_instructions,
                    function_locations,
                    &current_function,
                );

                // Show if within the last MAX_LINES_PER_FUNCTION lines of this function
                remaining_in_function < STACK_TRACE_MAX_LINES_PER_FUNCTION
            };

            if should_show {
                // Show skipped lines message if transitioning from skipping to showing
                if skipped_lines > 0 {
                    let indent = "│ ".repeat(call_stack.len());
                    result.push_str(&format!(
                        "{}├─ ... ({} lines skipped) ...\n",
                        indent, skipped_lines
                    ));
                    skipped_lines = 0;
                }

                let indent = "│ ".repeat(call_stack.len());
                let code_line = source_lines
                    .get(line_num.saturating_sub(1))
                    .unwrap_or(&"<line not found>")
                    .trim();

                if idx == latest_instructions.len() - 1 {
                    result.push_str(&format!(
                        "{}├─ {} {}\n",
                        indent, format!("line {}:", line_num).red(), code_line
                    ));
                } else {
                    result.push_str(&format!("{}├─ line {}: {}\n", indent, line_num, code_line));
                }
            } else {
                skipped_lines += 1;
            }
        }

        prev_function = current_function;
    }

    // Add summary
    result.push_str("\n");
    result.push_str("═══════════════════════════════════════════════════════════════\n");

    if !call_stack.is_empty() {
        result.push_str("\nCall stack:\n");
        for (i, (line, func)) in call_stack.iter().enumerate() {
            result.push_str(&format!("  {}. {} (line {})\n", i + 1, func, line));
        }
    }

    result
}

fn find_function_for_line(
    line_num: usize,
    function_locations: &BTreeMap<usize, String>,
) -> Option<String> {
    function_locations
        .range(..=line_num)
        .next_back()
        .map(|(_, func_name)| func_name.clone())
}

fn count_remaining_lines_in_function(
    current_idx: usize,
    latest_instructions: &VecDeque<LocationInSourceCode>,
    function_locations: &BTreeMap<usize, String>,
    current_function: &Option<String>,
) -> usize {
    let mut count = 0;

    for i in (current_idx + 1)..latest_instructions.len() {
        let line_num = latest_instructions[i];
        let func = find_function_for_line(line_num, function_locations);

        if &func != current_function {
            break;
        }
        count += 1;
    }

    count
}

pub fn execute_bytecode(
    bytecode: &Bytecode,
    public_input: &[F],
    private_input: &[F],
    source_code: &str,                            // debug purpose
    function_locations: &BTreeMap<usize, String>, // debug purpose
) -> ExecutionResult {
    let mut std_out = String::new();
    let mut latest_instructions = VecDeque::new();
    let first_exec = match execute_bytecode_helper(
        bytecode,
        public_input,
        private_input,
        MAX_MEMORY_SIZE / 2,
        false,
        &mut std_out,
        &mut latest_instructions,
    ) {
        Ok(first_exec) => first_exec,
        Err(err) => {
            println!(
                "\n{}",
                pretty_stack_trace(source_code, &latest_instructions, function_locations)
            );
            if !std_out.is_empty() {
                println!("╔══════════════════════════════════════════════════════════════╗");
                println!("║                         STD-OUT                              ║");
                println!("╚══════════════════════════════════════════════════════════════╝\n");
                print!("{}", std_out);
            }
            panic!("Error during bytecode execution: {}", err.to_string());
        }
    };
    execute_bytecode_helper(
        bytecode,
        public_input,
        private_input,
        first_exec.no_vec_runtime_memory,
        true,
        &mut String::new(),
        &mut latest_instructions,
    )
    .unwrap()
}

pub struct ExecutionResult {
    pub no_vec_runtime_memory: usize,
    pub public_memory_size: usize,
    pub memory: Memory,
    pub pcs: Vec<usize>,
    pub fps: Vec<usize>,
}

pub fn build_public_memory(public_input: &[F]) -> Vec<F> {
    // padded to a power of two
    let public_memory_len = (PUBLIC_INPUT_START + public_input.len()).next_power_of_two();
    let mut public_memory = F::zero_vec(public_memory_len);
    public_memory[PUBLIC_INPUT_START..][..public_input.len()].copy_from_slice(public_input);

    // "zero" vector
    for i in ZERO_VEC_PTR * VECTOR_LEN..(ZERO_VEC_PTR + 2) * VECTOR_LEN {
        public_memory[i] = F::ZERO;
    }

    // "one" vector
    public_memory[ONE_VEC_PTR * VECTOR_LEN] = F::ONE;
    for i in ONE_VEC_PTR * VECTOR_LEN + 1..(ONE_VEC_PTR + 1) * VECTOR_LEN {
        public_memory[i] = F::ZERO;
    }

    public_memory
        [POSEIDON_16_NULL_HASH_PTR * VECTOR_LEN..(POSEIDON_16_NULL_HASH_PTR + 2) * VECTOR_LEN]
        .copy_from_slice(&get_poseidon16().permute([F::ZERO; 16]));
    public_memory
        [POSEIDON_24_NULL_HASH_PTR * VECTOR_LEN..(POSEIDON_24_NULL_HASH_PTR + 1) * VECTOR_LEN]
        .copy_from_slice(&get_poseidon24().permute([F::ZERO; 24])[16..]);
    public_memory
}

fn execute_bytecode_helper(
    bytecode: &Bytecode,
    public_input: &[F],
    private_input: &[F],
    no_vec_runtime_memory: usize,
    final_execution: bool,
    std_out: &mut String,
    latest_instructions: &mut VecDeque<LocationInSourceCode>,
) -> Result<ExecutionResult, RunnerError> {
    let poseidon_16 = get_poseidon16(); // TODO avoid rebuilding each time
    let poseidon_24 = get_poseidon24();

    // set public memory
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
        (initial_ap + no_vec_runtime_memory).next_multiple_of(DIMENSION) / DIMENSION;

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

    while pc != bytecode.ending_pc {
        if pc >= bytecode.instructions.len() {
            return Err(RunnerError::PCOutOfBounds);
        }

        pcs.push(pc);
        fps.push(fp);

        cpu_cycles += 1;

        for hint in bytecode.hints.get(&pc).unwrap_or(&vec![]) {
            match hint {
                Hint::RequestMemory {
                    offset,
                    size,
                    vectorized,
                } => {
                    let size = size.read_value(&memory, fp)?.to_usize();

                    if *vectorized {
                        // find the next multiple of VECTOR_LEN
                        memory.set(fp + *offset, F::from_usize(ap_vec))?;
                        ap_vec += size;
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
                    let values_to_decompose = to_decompose
                        .iter()
                        .map(|v| Ok(v.read_value(&memory, fp)?.to_usize()))
                        .collect::<Result<Vec<_>, _>>()?;
                    let mut memory_index = fp + *res_offset;
                    for &value in &values_to_decompose {
                        for i in 0..F::bits() {
                            let bit = if value & (1 << i) != 0 {
                                F::ONE
                            } else {
                                F::ZERO
                            };
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
                            *std_out += &format!("[CHECKPOINT]\n");
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

                    let line_info = line_info.replace(";", "");
                    *std_out += &format!("\"{}\" -> {}\n", line_info, values.join(", "));
                    // does not increase PC
                }
                Hint::LocationReport { location } => {
                    if latest_instructions.back() != Some(location) {
                        latest_instructions.push_back(*location);
                    }
                    if latest_instructions.len() > STACK_TRACE_INSTRUCTIONS {
                        latest_instructions.pop_front();
                    }
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
                    let memory_address_res = res.memory_address(fp)?;
                    let ptr = memory.get(fp + shift_0)?;
                    let value = memory.get(ptr.to_usize() + shift_1)?;
                    memory.set(memory_address_res, value)?;
                } else {
                    let value = res.read_value(&memory, fp)?;
                    let ptr = memory.get(fp + shift_0)?;
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
                if condition_value != F::ZERO {
                    pc = dest.read_value(&memory, fp)?.to_usize();
                    fp = updated_fp.read_value(&memory, fp)?.to_usize();
                } else {
                    pc += 1;
                }

                jump_counts += 1;
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
                let slice_coeffs = (ptr_coeffs << *n_vars..(1 + ptr_coeffs) << *n_vars)
                    .map(|i| memory.get(i))
                    .collect::<Result<Vec<F>, _>>()?;
                let point = (0..*n_vars)
                    .map(|i| memory.get_ef_element(ptr_point + i * DIMENSION))
                    .collect::<Result<Vec<EF>, _>>()?;

                let eval = slice_coeffs.evaluate(&MultilinearPoint(point));
                memory.set_ef_element(ptr_res, eval)?;

                pc += 1;
            }
        }
    }

    debug_assert_eq!(pc, bytecode.ending_pc);
    pcs.push(pc);
    fps.push(fp);

    if final_execution {
        if !std_out.is_empty() {
            println!("╔══════════════════════════════════════════════════════════════╗");
            println!("║                         STD-OUT                              ║");
            println!("╚══════════════════════════════════════════════════════════════╝\n");
            print!("{}", std_out);
        }
        let runtime_memory_size = memory.0.len() - (PUBLIC_INPUT_START + public_input.len());
        println!(
            "\nBytecode size: {}",
            pretty_integer(bytecode.instructions.len())
        );
        println!("Public input size: {}", pretty_integer(public_input.len()));
        println!(
            "Private input size: {}",
            pretty_integer(private_input.len())
        );
        println!("Executed {} instructions", pretty_integer(cpu_cycles));
        println!(
            "Runtime memory: {} ({:.2}% vec)",
            pretty_integer(runtime_memory_size),
            (DIMENSION * (ap_vec - initial_ap_vec)) as f64 / runtime_memory_size as f64 * 100.0
        );
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
                "DotProductExtExt calls: {}",
                pretty_integer(dot_product_ext_ext_calls)
            );
        }
        if multilinear_eval_calls > 0 {
            println!(
                "MultilinearEval calls: {}",
                pretty_integer(multilinear_eval_calls)
            );
        }
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

        if false {
            println!("Low level instruction counts:");
            println!(
                "COMPUTE: {} ({} ADD, {} MUL)",
                add_counts + mul_counts,
                add_counts,
                mul_counts
            );
            println!("DEREF: {}", deref_counts);
            println!("JUMP: {}", jump_counts);
        }
    }

    let no_vec_runtime_memory = ap - initial_ap;
    Ok(ExecutionResult {
        no_vec_runtime_memory,
        public_memory_size,
        memory,
        pcs,
        fps,
    })
}
