#![cfg_attr(not(test), allow(unused_crate_dependencies))]

use std::marker::PhantomData;
use std::ops::Range;

use pcs::WhirBatchPcs;
use utils::*;
use vm::{EF, F};
use whir_p3::whir::config::{FoldingFactor, SecurityAssumption, WhirConfigBuilder};

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

pub fn build_batch_pcs()
-> WhirBatchPcs<F, EF, EF, MyMerkleHash, MyMerkleCompress, MY_DIGEST_ELEMS> {
    let base_pcs = WhirConfigBuilder {
        folding_factor: FoldingFactor::ConstantFromSecondRound(7, 4),
        soundness_type: SecurityAssumption::CapacityBound,
        merkle_hash: build_merkle_hash(),
        merkle_compress: build_merkle_compress(),
        pow_bits: 16,
        max_num_variables_to_send_coeffs: 6,
        rs_domain_initial_reduction_factor: 5,
        security_level: 128,
        starting_log_inv_rate: 1,
        base_field: PhantomData::<F>,
        extension_field: PhantomData::<EF>,
    };

    let extension_pcs = WhirConfigBuilder {
        folding_factor: FoldingFactor::ConstantFromSecondRound(4, 4),
        soundness_type: SecurityAssumption::CapacityBound,
        merkle_hash: build_merkle_hash(),
        merkle_compress: build_merkle_compress(),
        pow_bits: 16,
        max_num_variables_to_send_coeffs: 6,
        rs_domain_initial_reduction_factor: 2,
        security_level: 128,
        starting_log_inv_rate: 1,
        base_field: PhantomData::<EF>,
        extension_field: PhantomData::<EF>,
    };

    WhirBatchPcs(base_pcs, extension_pcs)
}
