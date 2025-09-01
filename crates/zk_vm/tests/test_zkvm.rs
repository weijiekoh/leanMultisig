use compiler::*;
use p3_field::PrimeCharacteristicRing;
use vm::*;
use zk_vm::{
    build_batch_pcs, prove_execution::prove_execution, verify_execution::verify_execution,
};

#[test]
fn test_zk_vm() {
    // Public input:  message_hash | all_public_keys | bitield
    // Private input: signatures = (randomness | chain_tips | merkle_path)
    let  program = r#"

    fn main() {
        for i in 0..1000 {
            x = malloc_vec(6);
            poseidon16(i + 3, i, x);
            poseidon24(i + 3, i, x + 2);
            dot_product(i*5, i, (x + 3) * 8, 1);
            dot_product(i*4, i + 7, (x + 4) * 8, 2);
        }
        for i in 0..1000 unroll {
            if 1 == 0 {
                return;
            }
        }
        return;
    }
   "#.to_string();

    let public_input = F::zero_vec(1 << 14);

    let private_input = vec![];

    // utils::init_tracing();
    let bytecode = compile_program(&program);
    let batch_pcs = build_batch_pcs();
    let proof_data = prove_execution(&bytecode, &public_input, &private_input, &batch_pcs);
    verify_execution(&bytecode, &public_input, proof_data, &batch_pcs).unwrap();
}
