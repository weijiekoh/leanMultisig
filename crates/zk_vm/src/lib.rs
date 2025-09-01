#![cfg_attr(not(test), allow(unused_crate_dependencies))]

use std::ops::Range;

use compiler::compile_program;
use vm::execute_bytecode;
use zk_vm_trace::*;

mod common;
pub mod prove_execution;
pub mod verify_execution;

const UNIVARIATE_SKIPS: usize = 4;

fn exec_column_groups() -> Vec<Range<usize>> {
    [
        (0..N_INSTRUCTION_COLUMNS_IN_AIR)
            .map(|i| i..i + 1)
            .collect::<Vec<_>>(),
        vec![
            N_INSTRUCTION_COLUMNS_IN_AIR..N_INSTRUCTION_COLUMNS_IN_AIR + N_MEMORY_VALUE_COLUMNS,
            N_INSTRUCTION_COLUMNS_IN_AIR + N_MEMORY_VALUE_COLUMNS
                ..N_INSTRUCTION_COLUMNS_IN_AIR + N_MEMORY_VALUE_COLUMNS + 1, // pc
            N_INSTRUCTION_COLUMNS_IN_AIR + N_MEMORY_VALUE_COLUMNS + 1
                ..N_INSTRUCTION_COLUMNS_IN_AIR + N_MEMORY_VALUE_COLUMNS + 2, // fp
            N_INSTRUCTION_COLUMNS_IN_AIR + N_MEMORY_VALUE_COLUMNS + 2
                ..N_INSTRUCTION_COLUMNS_IN_AIR + N_MEMORY_VALUE_COLUMNS + N_COMMITTED_EXEC_COLUMNS,
        ],
    ]
    .concat()
}

pub fn compile_and_run(program: &str, public_input: &[vm::F], private_input: &[vm::F]) {
    let bytecode = compile_program(program);
    execute_bytecode(&bytecode, &public_input, private_input);
}
