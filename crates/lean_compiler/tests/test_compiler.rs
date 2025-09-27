use lean_compiler::*;
use lean_vm::*;
use lean_vm::RunnerError;
use p3_symmetric::Permutation;
use utils::{get_poseidon16, get_poseidon24};
use p3_field::PrimeCharacteristicRing;
use std::collections::BTreeMap;

// Passes if the range check works when v < t
fn do_test_valid_range_check(v: usize, t: usize) {
    let result = range_check(v, t);
    if result.is_err() {
        println!("Error: {}", result.unwrap_err());
        assert!(false, "Range check failed");
    } else {
        assert!(result.is_ok());
    }
}

// Passes if the range check fails with OOM when v >= t
fn do_test_invalid_range_check(v: usize, t: usize) {
    let result = range_check(v, t); // should OOM
    if result.is_ok() {
        println!("Execution complete but the range check failed to OOM");
        assert!(false, "range check failed to catch OOM");
    }
    println!("result: {}", result.as_ref().unwrap_err());
    assert!(matches!(&result, Err(RunnerError::OutOfMemory)));
}

#[test]
fn test_valid_range_check() {
    // Check t = 70, v = 0..70
    let t = 70;
    for v in 0..t {
        do_test_valid_range_check(v, t);
    }

    // Check 0..[63, 64, 65]
    for t in vec![63, 64, 65] {
        for v in 0..t {
            do_test_valid_range_check(v, t);
        }
    }

    do_test_valid_range_check(64, 65);
}

// Should OOM since v >= M
#[test]
fn test_invalid_range_check_1() {
    let v = 16777216;
    for t in 0..70 {
        do_test_invalid_range_check(v, t);
    }
}

// Should OOM since t - 1 - v >= M
#[test]
fn test_invalid_range_check_2() {
    let v = 100;
    let t = 16777216 + 1 + v;
    do_test_invalid_range_check(v, t);
}

// Should OOM since v >= t
#[test]
fn test_invalid_range_check_3() {
    let t = 200;
    for v in 200..300 {
        do_test_invalid_range_check(v, t);
    }
}

// Should OOM since v == t
#[test]
fn test_invalid_range_check_4() {
    for i in 1..100 {
        do_test_invalid_range_check(i, i);
    }
}

// Should OOM since v > 0
#[test]
fn test_invalid_range_check_5() {
    for v in 1..100 {
        do_test_invalid_range_check(v, 0);
    }
}

//#[test]
//fn test_invalid_range_check_6() {
    //// TODO: fix this: when v is the prime order
    //do_test_invalid_range_check(2130706433, 0);
//}

fn range_check(v: usize, t: usize) -> Result<ExecutionResult, RunnerError> {
    let starting_frame_memory = 5;
    println!("v: {}; t: {}", v, t);
    let val = F::from_usize(v);

    // In the final version, these values will have to be set after a first execution pass
    let x = 1000;
    let i = 1003;
    let j = 1004;
    let k = 1005;
    let v_p = 1006;
    let t_p = 1007;

    let mut instructions = vec![];
    let hints = BTreeMap::new();

    // Store v in m[fp + x] by setting a pointer m[fp + vp] = fp + x and using deref to store 
    // v in m[m[fp + v_p] + 0]
    instructions.push(
        // computation: m[fp + v_p] = fp + x
        Instruction::Computation {
            operation: Operation::Add,
            arg_a: MemOrConstant::Constant(F::from_usize(x)),
            arg_c: MemOrFp::Fp,
            res: MemOrConstant::MemoryAfterFp { offset: v_p },
        }
    );

    instructions.push(
        // deref: val = m[m[fp + v_p] + 0] = m[fp + x]
        Instruction::Deref {
            shift_0: v_p,
            shift_1: 0,
            res: MemOrFpOrConstant::Constant(val),
        }
    );

    // Store t - 1 in m[fp + t_p] using constraint solving
    instructions.push(
        Instruction::Computation {
            operation: Operation::Add,
            arg_a: MemOrConstant::Constant(F::ONE),        // 1
            arg_c: MemOrFp::MemoryAfterFp { offset: t_p }, // m[fp + t_p] is unknown, so it will solve
                                                           // to t - 1
            res: MemOrConstant::Constant(F::from_usize(t)),
        }
    );

    // Range check step 1: 
    // Ensure that m[fp + i] == m[m[fp + x] + 0] aka m[val]
    // Fails if val >= M because of OOM
    if v == 64 || v == 65 {
        // Store 0 in m[m[fp + x] + 0]
        instructions.push(
            Instruction::Deref {
                shift_0: x,
                shift_1: 0,
                res: MemOrFpOrConstant::Constant(F::ZERO),
            }
        );
    } else if v < 64 {
        instructions.push(
            // m[m[fp + x] + 0] <- m[fp + i]
            Instruction::Deref {
                shift_0: x,
                shift_1: 0,
                res: MemOrFpOrConstant::MemoryAfterFp { offset: i },
            }
        );
    } else if v >= 16777216 {
        instructions.push(
            // m[m[fp + x] + 0] <- m[fp + v_p]
            Instruction::Deref {
                shift_0: x,
                shift_1: 0,
                res: MemOrFpOrConstant::MemoryAfterFp { offset: v_p },
            }
        );
    }

    // Range check step 2:
    // 2. Using ADD, ensure (via constraint-solving):
    // m[fp + j] + m[m[fp + x]] = (t - 1)
    // m[fp + j] = (t - 1) - m[m[fp + x]]
    instructions.push(
        Instruction::Computation {
            operation: Operation::Add,
            arg_a: MemOrConstant::MemoryAfterFp { offset: j },  // Unknown: m[fp + j] will be 
                                                                // solved to (t-1) - m[val]
            arg_c: MemOrFp::MemoryAfterFp { offset: x },        // Known:   m[fp + x] = m[val]
            res: MemOrConstant::MemoryAfterFp { offset: t_p }, // Known:   t - 1
        }
    );

    // If m[m[fp + j]] = m[t - 1 - v] is already initialised, set m[fp + k] = m[fp + j]
    if (t > v && t - 1 - v >= 64) || (t <= v) {
        instructions.push(
            Instruction::Computation {
                operation: Operation::Add,
                arg_a: MemOrConstant::MemoryAfterFp { offset: k },  // Unknown: m[fp + k]
                arg_c: MemOrFp::MemoryAfterFp { offset: j },        // Known:   m[fp + j]
                res: MemOrConstant::Constant(F::from_usize(0)),     // Known:   0
            }
        );
    }
    // When t - 1 - v < 64, we skip this constraint and let DEREF handle it

    // Range check step 3:
    // The goal is: Using DEREF, ensure `m[m[fp + j]] = m[fp + k]`
    // This step tries to access memory at address m[fp + j]. If m[fp + j] >= M, it fails.
    // This ensures that (t-1) - v < M, completing the range check.
    
    // The key insight: m[fp + j] = (t-1) - v from step 2
    // If (t-1) - v < 64, then m[fp + j] points to already-initialized public memory
    // If (t-1) - v >= 64, then m[fp + j] points to uninitialized memory
    
    // Range check step 3: Using DEREF, ensure we can access m[m[fp + j]]
    // This will fail if m[fp + j] >= M, proving that (t-1) - v < M
    // There is no additional constraint - we just read whatever value is there
    instructions.push(
        Instruction::Deref {
            shift_0: j,
            shift_1: 0,
            res: MemOrFpOrConstant::MemoryAfterFp { offset: k },
        }
    );
    
    //hints.insert(
        //instructions.len(),
        //vec![
            //Hint::Print {
                //line_info: "m[fp + i]".to_string(),
                //content: vec![MemOrConstant::MemoryAfterFp { offset: i }],
            //},
            //Hint::Print {
                //line_info: "m[fp + j]".to_string(),
                //content: vec![MemOrConstant::MemoryAfterFp { offset: j }],
            //},
            //Hint::Print {
                //line_info: "m[fp + k]".to_string(),
                //content: vec![MemOrConstant::MemoryAfterFp { offset: k }],
            //},
        //],
    //);

    instructions.push(
        Instruction::Jump {
            condition: MemOrConstant::Constant(F::ONE),
            dest: MemOrConstant::Constant(F::from_usize(instructions.len() + 1)),
            updated_fp: MemOrFp::Fp,
        }
    );
    instructions.push(
        Instruction::Jump {
            condition: MemOrConstant::Constant(F::ONE),
            dest: MemOrConstant::Constant(F::from_usize(0)),
            updated_fp: MemOrFp::Fp,
        }
    );

    let ending_pc = instructions.len() - 1;
    let bytecode = Bytecode {
        instructions,
        hints,
        starting_frame_memory,
        ending_pc,
    };

    println!("Raw Bytecode:\n{}", bytecode.to_string());
    println!("starting_frame_memory: {}", bytecode.starting_frame_memory);

    // Execute the bytecode
    let execution_result = execute_bytecode(
        &bytecode,
        &[], // public input
        &[], // private input 
        "", // no source code for debug
        &std::collections::BTreeMap::new(), // no function locations
        false, // no profiler
    );
    execution_result
}

#[test]
fn test_add_and_deref() {

    // Build raw bytecode instructions
    let instructions = vec![
        // m[fp + 2] = 3 + fp
        // ADD 3 + fp and store it in m[fp + 2]
        Instruction::Computation {
            operation: Operation::Add,
            arg_a: MemOrConstant::Constant(F::from_usize(3)),
            arg_c: MemOrFp::Fp,
            res: MemOrConstant::MemoryAfterFp { offset: 2 },
        },
        // 123 = m[m[fp + 2] + 0] (write 123 to memory location)
        // DEREF: write 123 to m[m[fp + 2] + 0]
        Instruction::Deref {
            shift_0: 2,
            shift_1: 0,
            res: MemOrFpOrConstant::Constant(F::from_usize(123)),
        },

        // ADD 6 + fp and store it in m[fp + 4]
        Instruction::Computation {
            operation: Operation::Add,
            arg_a: MemOrConstant::Constant(F::from_usize(6)),
            arg_c: MemOrFp::Fp,
            res: MemOrConstant::MemoryAfterFp { offset: 4 },
        },

        // DEREF: write 456 to m[m[fp + 4] + 0]
        Instruction::Deref {
            shift_0: 4,
            shift_1: 0,
            res: MemOrFpOrConstant::Constant(F::from_usize(456)),
        },

        Instruction::Deref {
            shift_0: 4,  // Read address from m[fp + 4] (which is 71)
            shift_1: 0,  // No additional offset
            res: MemOrFpOrConstant::MemoryAfterFp { offset: 6 }, // Store result in m[fp + 6]
        },

        // ADD 0 + m[fp + 6] and store it in m[m[fp + 6]]
        // 0 = 0 + m[fp + 6]
        Instruction::Computation {
            operation: Operation::Add,
            arg_a: MemOrConstant::Constant(F::ZERO),
            arg_c: MemOrFp::MemoryAfterFp { offset: 5 },
            res: MemOrConstant::Constant(F::ZERO),
        },
        Instruction::Jump {
            condition: MemOrConstant::Constant(F::ONE),
            dest: MemOrConstant::Constant(F::from_usize(6)),
            updated_fp: MemOrFp::MemoryAfterFp { offset: 5 },
        },
    ];

    // Add print hint at PC 2
    let mut hints = BTreeMap::new();
    hints.insert(
        2,
        vec![Hint::Print {
            line_info: "print(a[0]);".to_string(),
            content: vec![MemOrConstant::MemoryAfterFp { offset: 3 }],
        }],
    );

    hints.insert(
        4,
        vec![Hint::Print {
            line_info: "print #2".to_string(),
            content: vec![MemOrConstant::MemoryAfterFp { offset: 6 }],
        }],
    );

    let ending_pc = instructions.len() - 1;

    let bytecode = Bytecode {
        instructions,
        hints,
        starting_frame_memory: 5,
        ending_pc,
    };

    println!("Raw Bytecode:\n\n{}", bytecode.to_string());
    println!("starting_frame_memory: {}", bytecode.starting_frame_memory);

    // Execute the bytecode
    let execution_result = execute_bytecode(
        &bytecode,
        &[], // no public input
        &[], // no private input 
        "", // no source code for debug
        &std::collections::BTreeMap::new(), // no function locations
        false, // no profiler
    ).unwrap();

    println!("Execution completed!");
    println!("Memory size: {}", execution_result.memory.0.len());
    println!("PC history: {:?}", execution_result.pcs);
    println!("FP history: {:?}", execution_result.fps);
}

#[test]
#[should_panic]
fn test_duplicate_function_name() {
    let program = r#"
    fn a() -> 1 {
        return 0;
    }

    fn a() -> 1 {
        return 1;
    }

    fn main() {
        a();
        return;
    }
    "#;
    compile_and_run(program, &[], &[], false);
}

#[test]
#[should_panic]
fn test_duplicate_constant_name() {
    let program = r#"
    const A = 1;
    const A = 0;

    fn main() {
        return;
    }
    "#;
    compile_and_run(program, &[], &[], false);
}

#[test]
fn test_fibonacci_program() {
    // a program to check the value of the 30th Fibonacci number (832040)
    let program = r#"
    fn main() {
        fibonacci(0, 1, 0, 30);
        return;
    }

    fn fibonacci(a, b, i, n) {
        if i == n {
            print(a);
            return;
        }
        fibonacci(b, a + b, i + 1, n);
        return;
    }
   "#;
    compile_and_run(program, &[], &[], false);
}

#[test]
fn test_edge_case_0() {
    let program = r#"
    fn main() {
        a = malloc(1);
        a[0] = 0;
        for i in 0..1 {
            x = 1 + a[i];
        }
        for i in 0..1 {
            y = 1 + a[i];
        }
        return;
    }
   "#;
    compile_and_run(program, &[], &[], false);
}

#[test]
fn test_edge_case_1() {
    let program = r#"
    fn main() {
        a = malloc(1);
        a[0] = 0;
        assert a[8 - 8] == 0;
        return;
    }
   "#;
    compile_and_run(program, &[], &[], false);
}

#[test]
fn test_edge_case_2() {
    let program = r#"
    fn main() {
        for i in 0..5 unroll {
            x = i;
            print(x);
        }
        for i in 0..3 unroll {
            x = i;
            print(x);
        }
        return;
    }
   "#;
    compile_and_run(program, &[], &[], false);
}

#[test]
fn test_decompose_bits() {
    let program = r#"
    const A = 2 ** 30 - 1;
    const B = 2 ** 10 - 1;
    fn main() {
        a = decompose_bits(A, B);
        for i in 0..62  {
            print(a[i]);
        }
        return;
    }
   "#;
    compile_and_run(program, &[], &[], false);
}

#[test]
fn test_unroll() {
    // a program to check the value of the 30th Fibonacci number (832040)
    let program = r#"
    fn main() {
        for i in 0..5 unroll {
            for j in i..2*i unroll {
                print(i, j);
            }
        }
        return;
    }
   "#;
    compile_and_run(program, &[], &[], false);
}

#[test]
fn test_rev_unroll() {
    // a program to check the value of the 30th Fibonacci number (832040)
    let program = r#"
    fn main() {
        print(785 * 78 + 874 - 1);
        return;
    }
   "#;
    compile_and_run(program, &[], &[], false);
}

#[test]
fn test_mini_program_0() {
    let program = r#"
    fn main() {
        for i in 0..5 {
            for j in i..2*i*(2+1) {
                print(i, j);
                if i == 4 {
                    if j == 7 {
                        break;
                    }
                }
            }
        }
        return;
    }
   "#;
    compile_and_run(program, &[], &[], false);
}

#[test]
fn test_mini_program_1() {
    let program = r#"
    const N = 10;

    fn main() {
        arr = malloc(N);
        fill_array(arr);
        print_array(arr);
        return;
    }

    fn fill_array(arr) {
        for i in 0..N {
            if i == 0 {
                arr[i] = 10;
            } else {
                if i == 1 {
                    arr[i] = 20;
                } else {
                    if i == 2 {
                        arr[i] = 30;
                    } else {
                        i_plus_one = i + 1;
                        arr[i] = i_plus_one;
                    }
                }
            }
        }
        return;
    }

    fn print_array(arr) {
        for i in 0..N {
            arr_i = arr[i];
            print(arr_i);
        }
        return;
    }
   "#;
    compile_and_run(program, &[], &[], false);
}

#[test]
fn test_mini_program_2() {
    let program = r#"
    fn main() {
        for i in 0..10 {
            for j in i..10 {
                for k in j..10 {
                    sum, prod = compute_sum_and_product(i, j, k);
                    if sum == 10 {
                        print(i, j, k, prod);
                    }
                }
            }
        }
        return;
    }

    fn compute_sum_and_product(a, b, c) -> 2 {
        s1 = a + b;
        sum = s1 + c;
        p1 = a * b;
        product = p1 * c;
        return sum, product;
    }
   "#;
    compile_and_run(program, &[], &[], false);
}

#[test]
fn test_mini_program_3() {
    let program = r#"
    fn main() {
        a = public_input_start / 8;
        b = a + 1;
        c = malloc_vec(2);
        poseidon16(a, b, c);

        c_shifted = c * 8;
        d_shifted = (c + 1) * 8;

        for i in 0..8 {
            cc = c_shifted[i];
            print(cc);
        }
        for i in 0..8 {
            dd = d_shifted[i];
            print(dd);
        }
        return;
    }
   "#;
    let mut public_input: [F; 16] = (0..16).map(F::new).collect::<Vec<F>>().try_into().unwrap();
    compile_and_run(program, &public_input, &[], false);

    get_poseidon16().permute_mut(&mut public_input);
    let _ = public_input;
}

#[test]
fn test_mini_program_4() {
    let program = r#"
    fn main() {
        a = public_input_start / 8;
        c = a + 2;
        f = malloc_vec(1);
        poseidon24(a, c, f);

        f_shifted = f * 8;
        for j in 0..8 {
            print(f_shifted[j]);
        }
        return;
    }
   "#;
    let mut public_input: [F; 24] = (0..24).map(F::new).collect::<Vec<F>>().try_into().unwrap();
    compile_and_run(program, &public_input, &[], false);

    get_poseidon24().permute_mut(&mut public_input);
    dbg!(&public_input[16..]);
}

#[test]
fn test_inlined() {
    let program = r#"
    fn main() {
        x = 1;
        y = 2;
        i, j, k = func_1(x, y);
        assert i == 2;
        assert j == 3;
        assert k == 2130706432;

        g = malloc_vec(1);
        h = malloc_vec(1);
        g_ptr = g * 8;
        h_ptr = h * 8;
        for i in 0..8 {
            g_ptr[i] = i;
        }
        for i in 0..8 unroll {
            h_ptr[i] = i;
        }
        assert_vectorized_eq_1(g, h);
        assert_vectorized_eq_2(g, h);
        assert_vectorized_eq_3(g, h);
        assert_vectorized_eq_4(g, h);
        assert_vectorized_eq_5(g, h);
        return;
    }

    fn func_1(a, b) inline -> 3 {
        x = a * b;
        y = a + b;
        return x, y, a - b;
    }

    fn assert_vectorized_eq_1(x, y) {
        x_ptr = x * 8;
        y_ptr = y * 8;
        for i in 0..4 unroll {
            assert x_ptr[i] == y_ptr[i];
        }
        for i in 4..8 {
            assert x_ptr[i] == y_ptr[i];
        }
        return;
    }

    fn assert_vectorized_eq_2(x, y) inline {
        x_ptr = x * 8;
        y_ptr = y * 8;
        for i in 0..4 unroll {
            assert x_ptr[i] == y_ptr[i];
        }
        for i in 4..8 {
            assert x_ptr[i] == y_ptr[i];
        }
        return;
    }
    fn assert_vectorized_eq_3(x, y) inline {
        u = x + 7;
        assert_vectorized_eq_1(u-7, y * 7 / 7);
        return;
    }
    fn assert_vectorized_eq_4(x, y) {
        dot_product(x * 8, pointer_to_one_vector * 8, y * 8, 1);
        dot_product(x * 8 + 3, pointer_to_one_vector * 8, y * 8 + 3, 1);
        return;
    }
    fn assert_vectorized_eq_5(x, y) inline {
        dot_product(x * 8, pointer_to_one_vector * 8, y * 8, 1);
        dot_product(x * 8 + 3, pointer_to_one_vector * 8, y * 8 + 3, 1);
        return;
    }
   "#;
    compile_and_run(program, &[], &[], false);
}

#[test]
fn test_match() {
    let program = r#"
    fn main() {
        for x in 0..3 unroll {
            func_match(x);
        }
        for x in 0..2 unroll {
            match x {
                0 => {
                    y = 10 * (x + 8);
                    z = 10 * y;
                    print(z);
                }
                1 => {
                    y = 10 * x;
                    z = func_2(y);
                    print(z);
                }
            }
        }
        return;
    }

    fn func_match(x) inline {
        match x {
            0 => {
                print(41);
            }
            1 => {
                y = func_1(x);
                print(y + 1);
            }
            2 => {
                y = 10 * x;
                print(y);
            }
        }
        return;
    }

    fn func_1(x) -> 1 {
        return x * x * x * x;
    }

    fn func_2(x) inline -> 1 {
        return x * x * x * x * x * x;
    }
   "#;
    compile_and_run(program, &[], &[], false);
}

// #[test]
// fn inline_bug_mre() {
//     let program = r#"
//     fn main() {
//         boolean(0);
//         return;
//     }

//     fn boolean(a) inline -> 1 {
//         if a == 0 {
//             return 0;
//         }
//         return 1;
//     }
//    "#;
//     compile_and_run(program, &[], &[]);
// }
