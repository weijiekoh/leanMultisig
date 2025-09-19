#![cfg_attr(not(test), allow(unused_crate_dependencies))]

mod examples;

use crate::examples::prove_poseidon2::prove_poseidon2;
use whir_p3::whir::config::{FoldingFactor, SecurityAssumption};

fn main() {
    let benchmark = prove_poseidon2(
        17,
        17,
        4,
        FoldingFactor::new(7, 4),
        1,
        SecurityAssumption::CapacityBound,
        16,
        128,
        5,
        3,
        true,
    );
    println!("\n{benchmark}");
}
