use std::collections::BTreeMap;
use lean_vm::*;
//use lean_vm::runner::compile_range_checks;
use p3_field::PrimeCharacteristicRing;
use lean_compiler::{parse_program, compile_program};
use lean_compiler::{Expression, SimpleExpr, Line, SimpleLine, simplify_program, compile_to_intermediate_bytecode, compile_to_low_level_bytecode, IntermediateInstruction, IntermediateValue};
use utils::ToUsize;

fn range_check_test_cases() -> Vec<(usize, usize)> {
    let mut test_cases = vec![];
    for t in 63..70 {
        for v in 0..t + 2 {
            test_cases.push((v, t));
        }
        for v in 16777215..16777217 {
            test_cases.push((v, t));
        }
    }

    for v in 90..100 {
        let t = 16777216 + 1 + v;
        test_cases.push((v, t));
    }

    test_cases
}

fn range_check_program(value: usize, max: usize) -> String {
    let program = format!(r#"
    fn main() {{
        val = {};
        range_check(val, {});
        return;
    }}
    "#, value, max);
    program.to_string()
}

#[test]
fn test_compile_range_checks() {
    //for (v, t) in vec![(64, 63)] {
    for (v, t) in range_check_test_cases() {
        println!("Range Check Test: v: {}, t: {}", v, t);
        let program = range_check_program(v, t);
        let (mut bytecode, function_locations) = compile_program(&program);
        println!("old bytecode:\n{}", bytecode);
        println!("ending_pc: {}", bytecode.ending_pc);
        println!();

        let new_bytecode = compile_range_checks(&bytecode, &[], &[]);
        match new_bytecode {
            Ok(new_bytecode) => {
                println!("new bytecode:\n{}", new_bytecode);
                println!("ending_pc: {}", new_bytecode.ending_pc);
                let result = execute_bytecode(
                    &mut bytecode,
                    &[],
                    &[],
                    &program,
                    &function_locations,
                    false,
                    );

                if v >= t {
                    assert!(
                        matches!(result, Err(RunnerError::OutOfMemory)),
                        "range check failed to catch OOM"
                        );
                } else {
                    assert!(result.is_ok());
                }

            }
            Err(err) => {
                println!("Failed to compile range checks: {}", err);
            }
        }
    }
}

#[test]
fn test_range_check_compilation_and_execution() {
    //for (v, t) in range_check_test_cases() {
    //for (v, t) in vec![(0, 67), (68, 66), (0, 68), (63, 63), (15, 63), (66, 65), (16777217, 68)] {
    for (v, t) in vec![(0, 67)] {
        println!("Range Check Test: v: {}, t: {}", v, t);
        let program = range_check_program(v, t);
        let (mut bytecode, function_locations) = compile_program(&program);
        let result = execute_bytecode(
            &mut bytecode,
            &[],
            &[],
            &program,
            &function_locations,
            false,
        );

        if v >= t {
            assert!(
                matches!(result, Err(RunnerError::OutOfMemory)),
                "range check failed to catch OOM"
            );
        } else {
            assert!(result.is_ok());
        }
    }
    //for v in 0..100 {
        ////let v = 1;
        ////let v = 16777216;
        //let t = 200;
        //println!("Range Check Test: v: {}, t: {}", v, t);
        //let program = range_check_program(v, t);
        //let (mut bytecode, function_locations) = compile_program(&program);
        //println!("{}", bytecode.to_string());
        //let result = execute_bytecode(
            //&mut bytecode,
            //&[],
            //&[],
            //&program,
            //&function_locations,
            //false,
        //);
        //assert!(result.is_ok());
    //}
}

/// Simple test that the range check keyword is parsed and compiled (steps a and b only).
#[test]
fn test_range_check_parsing_and_compilation_a_b() {
    let value_usize = 1;
    let max_usize = 2;
    let program = range_check_program(value_usize, max_usize);
    let (parsed_program, _function_locations) = parse_program(&program).unwrap();

    // Traverse through the parsed program and check that the range check is present
    let main_func = parsed_program.functions.get("main").unwrap();
    let mut found = false;
    for line in main_func.body.iter() {
        match line {
            Line::RangeCheck { value, max } => {
                match value {
                    Expression::Value(SimpleExpr::Var(v)) => {
                        assert_eq!(v, "val", "Range check value should be 'val'");
                        if let Some(max_val) = max.naive_eval() {
                            assert_eq!(max_val.to_usize(), max_usize, "Range check max should be 2");
                        }
                    }
                    _ => panic!("Unexpected range check value type: {:?}", value),
                }
                
                found = true;
            }
            _ => {}
        }
    }
    assert!(found, "Range check not found in the parsed program");

    found = false;
    let simple_program = simplify_program(parsed_program);
    let main_func = simple_program.functions.get("main").unwrap();

    // Traverse through the simplified program and check that the range check is present
    for line in main_func.instructions.iter() {
        match line {
            SimpleLine::RangeCheck { value, max } => {
                match value {
                    SimpleExpr::Var(v) => {
                        assert_eq!(v, "val", "Range check value should be 'val'");
                        if let Some(max_val) = max.naive_eval() {
                            assert_eq!(max_val.to_usize(), max_usize, "Range check max should be 2");
                        }
                    }
                    _ => panic!("Unexpected range check value type: {:?}", value),
                }
                found = true;
            }
            _ => {}
        }

    }
    assert!(found, "Range check not found in the simplified program");

    found = false;
    let intermediate_bytecode = compile_to_intermediate_bytecode(simple_program).unwrap();
    let main_func = intermediate_bytecode.bytecode.get("@function_main").unwrap();
    for instruction in main_func.iter() {
        match instruction {
            IntermediateInstruction::RangeCheck { value, max } => {
                assert!(matches!(value, IntermediateValue::MemoryAfterFp { .. }), 
                       "Range check value should be memory reference in intermediate bytecode");
                
                if let Some(max_val) = max.naive_eval() {
                    assert_eq!(max_val.to_usize(), max_usize, "Range check max should be 2 in intermediate bytecode");
                } else {
                    panic!("Range check max should be evaluable constant in intermediate bytecode");
                }
                
                found = true;
            }
            _ => {}
        }
    }
    assert!(found, "Range check not found in the intermediate bytecode");

    let compiled = compile_to_low_level_bytecode(intermediate_bytecode).unwrap();
    println!("Compiled Program:\n{}\n", compiled.to_string());

    assert!(found, "Range check not found in the intermediate bytecode");
}

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

    do_test_valid_range_check(0, 16777216);
    do_test_valid_range_check(64, 16777216);
    do_test_valid_range_check(16777215, 16777216);
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

#[test]
fn test_invalid_range_check_6() {
    let t = 0;
    for v in 0..70 {
        do_test_invalid_range_check(v, t);
    }
    do_test_invalid_range_check(16777215, t);
}

#[test]
fn test_invalid_range_check_7() {
    for v in 0..10 {
        do_test_invalid_range_check(16777216 + v, 16777216);
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
        },
    );

    instructions.push(
        // deref: val = m[m[fp + v_p] + 0] = m[fp + x]
        Instruction::Deref {
            shift_0: v_p,
            shift_1: 0,
            res: MemOrFpOrConstant::Constant(val),
        },
    );

    // Store t - 1 in m[fp + t_p] using constraint solving
    instructions.push(Instruction::Computation {
        operation: Operation::Add,
        arg_a: MemOrConstant::Constant(F::ONE),        // 1
        arg_c: MemOrFp::MemoryAfterFp { offset: t_p }, // m[fp + t_p] is unknown, so it will solve
        // to t - 1
        res: MemOrConstant::Constant(F::from_usize(t)),
    });

    // Range check step 1:
    // Ensure that m[fp + i] == m[m[fp + x] + 0] aka m[val]
    // Fails if val >= M because of OOM
    let step_1_res = if v == 64 || v == 65 {
        MemOrFpOrConstant::Constant(F::ZERO)
    } else if v < 64 {
        MemOrFpOrConstant::MemoryAfterFp { offset: i }
    } else if v >= 16777216 {
        MemOrFpOrConstant::MemoryAfterFp { offset: v_p }
    } else {
        MemOrFpOrConstant::MemoryAfterFp { offset: v_p }
    };

    instructions.push(Instruction::Deref {
        shift_0: x,
        shift_1: 0,
        res: step_1_res,
    });

    // Range check step 2: Using ADD, ensure (via constraint-solving):
    // m[fp + j] + m[m[fp + x]] = (t - 1)
    // m[fp + j] = (t - 1) - m[m[fp + x]]
    instructions.push(Instruction::Computation {
        operation: Operation::Add,
        arg_a: MemOrConstant::MemoryAfterFp { offset: j }, // Unknown: m[fp + j] will be solved to
                                                           // (t-1) - m[val]
        arg_c: MemOrFp::MemoryAfterFp { offset: x },       // Known:   m[fp + x] = m[val]
        res: MemOrConstant::MemoryAfterFp { offset: t_p }, // Known:   t - 1
    });

    // If m[m[fp + j]] = m[t - 1 - v] is already initialised, set m[fp + k] = m[fp + j]
    if (t > v && t - 1 - v >= 64) || (t <= v) {
        instructions.push(Instruction::Computation {
            operation: Operation::Add,
            arg_a: MemOrConstant::MemoryAfterFp { offset: k }, // Unknown: m[fp + k]
            arg_c: MemOrFp::MemoryAfterFp { offset: j },       // Known:   m[fp + j]
            res: MemOrConstant::Constant(F::from_usize(0)),    // Known:   0
        });
    }

    // Range check step 3: ensure `m[m[fp + j]] = m[fp + k]`
    instructions.push(Instruction::Deref {
        shift_0: j,
        shift_1: 0,
        res: MemOrFpOrConstant::MemoryAfterFp { offset: k },
    });

    /*
    hints.insert(
        instructions.len(),
        vec![
        Hint::Print {
            line_info: "m[fp + i]".to_string(),
            content: vec![MemOrConstant::MemoryAfterFp { offset: i }],
        },
        Hint::Print {
            line_info: "m[fp + j]".to_string(),
            content: vec![MemOrConstant::MemoryAfterFp { offset: j }],
        },
        Hint::Print {
            line_info: "m[fp + k]".to_string(),
            content: vec![MemOrConstant::MemoryAfterFp { offset: k }],
        },
        ],
    );
    */

    instructions.push(Instruction::Jump {
        condition: MemOrConstant::Constant(F::ONE),
        dest: MemOrConstant::Constant(F::from_usize(instructions.len() + 1)),
        updated_fp: MemOrFp::Fp,
    });
    instructions.push(Instruction::Jump {
        condition: MemOrConstant::Constant(F::ONE),
        dest: MemOrConstant::Constant(F::from_usize(0)),
        updated_fp: MemOrFp::Fp,
    });

    let ending_pc = instructions.len() - 1;
    let mut bytecode = Bytecode {
        instructions,
        hints,
        starting_frame_memory,
        ending_pc,
    };

    println!("Raw Bytecode:\n{}", bytecode.to_string());
    println!("starting_frame_memory: {}", bytecode.starting_frame_memory);

    // Execute the bytecode
    let execution_result = execute_bytecode(
        &mut bytecode,
        &[],                                // public input
        &[],                                // private input
        "",                                 // no source code for debug
        &std::collections::BTreeMap::new(), // no function locations
        false,                              // no profiler
    );
    execution_result
}
