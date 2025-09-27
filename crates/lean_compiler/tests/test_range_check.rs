use lean_vm::RunnerError;
use lean_vm::*;
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
    do_test_invalid_range_check(16777215, 0);
    do_test_invalid_range_check(16777216, 16777216);
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

    // Range check step 2:
    // 2. Using ADD, ensure (via constraint-solving):
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
        &[],                                // public input
        &[],                                // private input
        "",                                 // no source code for debug
        &std::collections::BTreeMap::new(), // no function locations
        false,                              // no profiler
    );
    execution_result
}
