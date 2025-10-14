use std::collections::BTreeMap;

use lean_vm::*;
use lean_runner::{execute_bytecode_helper, ExecutionHistory};

pub use crate::{
    lang::{Line, Expression, SimpleExpr, ConstExpression},
    a_simplify_lang::{SimpleLine, simplify_program},
    b_compile_intermediate::compile_to_intermediate_bytecode,
    c_compile_to_low_level_bytecode::compile_to_low_level_bytecode,
    parser::parse_program,
    intermediate_bytecode::{IntermediateInstruction, IntermediateValue},
    d_compile_range_checks::{compile_range_checks, RangeCheckInfo, is_undef},
};

mod a_simplify_lang;
mod b_compile_intermediate;
mod c_compile_to_low_level_bytecode;
mod d_compile_range_checks;
mod intermediate_bytecode;
mod lang;
mod parser;
mod precompiles;
pub use precompiles::PRECOMPILES;


pub fn compile_program(program: &str) -> (Bytecode, BTreeMap<usize, String>) {
    let (parsed_program, function_locations) = parse_program(program).unwrap();
    // println!("Parsed program: {}", parsed_program.to_string());
    let simple_program = simplify_program(parsed_program);
    // println!("Simplified program: {}", simple_program.to_string());
    let intermediate_bytecode = compile_to_intermediate_bytecode(simple_program).unwrap();
    // println!("Intermediate Bytecode:\n\n{}", intermediate_bytecode.to_string());
    let mut compiled = compile_to_low_level_bytecode(intermediate_bytecode).unwrap();
    //println!("Compiled Program:\n\n{}", compiled.to_string());
    
    // Check if range checks exist - if so, compile them
    if compiled.hints.values().any(|hints| 
        hints.iter().any(|h| matches!(h, Hint::RangeCheck { .. }))
    ) {
        // First execution to get execution trace for range check compilation
        let mut std_out = String::new();
        let mut instruction_history = ExecutionHistory::default();
        let first_exec = execute_bytecode_helper(
            &compiled,
            &[], // No public input for range check compilation
            &[], // No private input for range check compilation
            MAX_RUNNER_MEMORY_SIZE / 2,
            false,
            &mut std_out,
            &mut instruction_history,
            false,
            &function_locations,
        ).unwrap();
        
        // Compile range checks using the execution result
        compiled = compile_range_checks(&first_exec, &compiled).unwrap();
    }
    
    (compiled, function_locations)
}

pub fn compile_and_run(program: &str, public_input: &[F], private_input: &[F], profiler: bool) {
    let (mut bytecode, function_locations) = compile_program(program);
    let _r = execute_bytecode(
        &mut bytecode,
        public_input,
        private_input,
        program,
        &function_locations,
        profiler,
    );
}

#[derive(Debug, Clone, Default)]
struct Counter(usize);

impl Counter {
    const fn next(&mut self) -> usize {
        let val = self.0;
        self.0 += 1;
        val
    }

    const fn new() -> Self {
        Self(0)
    }
}
