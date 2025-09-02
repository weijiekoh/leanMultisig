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
    let program = r#"
    
    fn main() {
        for i in 0..1000 unroll {  if 1 == 0 {  return; } } // increase bytecode size artificially

        for i in 0..1000 {
            x = malloc_vec(6);
            poseidon16(i + 3, i, x);
            poseidon24(i + 3, i, x + 2);
            dot_product(i*2, i, (x + 3) * 8, 1);
            dot_product(i*3, i + 7, (x + 4) * 8, 2);
        }
        
        point = malloc_vec(10);
        point_ptr = 8 * point;
        for i in 0..10 {
            point_ptr[8*i] = 785 + i;
            point_ptr[1 + 8*i] = 4152 - i;
            point_ptr[2 + 8*i] = 471*82 + i*i;
            point_ptr[3 + 8*i] = 7577 + i;
            point_ptr[4 + 8*i] = 676 - i;
            point_ptr[5 + 8*i] = 0;
            point_ptr[6 + 8*i] = 0;
            point_ptr[7 + 8*i] = 0;
        }

        res1 = malloc_vec(1);
        multilinear_eval(2**3, point, res1, 10);

        res2 = malloc_vec(1);
        multilinear_eval(3, point, res2, 7);

        return;
    }
   "#
    .to_string();


    let public_input = (0..(1 << 13) - PUBLIC_INPUT_START).map(|i| F::from_usize(i)).collect::<Vec<_>>();

    let private_input = (0..1 << 13).map(|i| F::from_usize(i).square()).collect::<Vec<_>>();

    // utils::init_tracing();
    let bytecode = compile_program(&program);
    let batch_pcs = build_batch_pcs();
    let proof_data = prove_execution(&bytecode, &public_input, &private_input, &batch_pcs);
    verify_execution(&bytecode, &public_input, proof_data, &batch_pcs).unwrap();
}
