use std::collections::BTreeMap;
use std::fmt::Display;
use std::fmt::Formatter;

use p3_field::PrimeCharacteristicRing;
use p3_field::PrimeField64;
use utils::ToUsize;

use crate::{F, lang::ConstExpression};
use vm::*;

#[derive(Debug, Clone)]
pub struct IntermediateBytecode {
    pub bytecode: BTreeMap<Label, Vec<IntermediateInstruction>>,
    pub match_blocks: Vec<Vec<Vec<IntermediateInstruction>>>,
    pub memory_size_per_function: BTreeMap<String, usize>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IntermediateValue {
    Constant(ConstExpression),
    Fp,
    MemoryAfterFp { offset: ConstExpression }, // m[fp + offset]
}

impl From<ConstExpression> for IntermediateValue {
    fn from(value: ConstExpression) -> Self {
        IntermediateValue::Constant(value)
    }
}
impl TryFrom<HighLevelOperation> for Operation {
    type Error = String;

    fn try_from(value: HighLevelOperation) -> Result<Self, Self::Error> {
        match value {
            HighLevelOperation::Add => Ok(Operation::Add),
            HighLevelOperation::Mul => Ok(Operation::Mul),
            _ => Err(format!("Cannot convert {:?} to +/x", value)),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum IntermediaryMemOrFpOrConstant {
    MemoryAfterFp { offset: ConstExpression }, // m[fp + offset]
    Fp,
    Constant(ConstExpression),
}

impl IntermediateValue {
    pub fn label(label: Label) -> Self {
        Self::Constant(ConstExpression::label(label))
    }

    pub fn is_constant(&self) -> bool {
        matches!(self, IntermediateValue::Constant(_))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum HighLevelOperation {
    Add,
    Mul,
    Sub,
    Div, // in the end everything compiles to either Add or Mul
    Exp, // Exponentiation, only for const expressions
    Mod, // Modulo, only for const expressions
}

impl HighLevelOperation {
    pub fn eval(&self, a: F, b: F) -> F {
        match self {
            HighLevelOperation::Add => a + b,
            HighLevelOperation::Mul => a * b,
            HighLevelOperation::Sub => a - b,
            HighLevelOperation::Div => a / b,
            HighLevelOperation::Exp => a.exp_u64(b.as_canonical_u64()),
            HighLevelOperation::Mod => F::from_usize(a.to_usize() % b.to_usize()),
        }
    }
}

#[derive(Debug, Clone)]
pub enum IntermediateInstruction {
    Computation {
        operation: Operation,
        arg_a: IntermediateValue,
        arg_c: IntermediateValue,
        res: IntermediateValue,
    },
    Deref {
        shift_0: ConstExpression,
        shift_1: ConstExpression,
        res: IntermediaryMemOrFpOrConstant,
    }, // res = m[m[fp + shift_0]]
    Panic,
    Jump {
        dest: IntermediateValue,
        updated_fp: Option<IntermediateValue>,
    },
    JumpIfNotZero {
        condition: IntermediateValue,
        dest: IntermediateValue,
        updated_fp: Option<IntermediateValue>,
    },
    Poseidon2_16 {
        arg_a: IntermediateValue, // vectorized pointer, of size 1
        arg_b: IntermediateValue, // vectorized pointer, of size 1
        res: IntermediateValue,   // vectorized pointer, of size 2
    },
    Poseidon2_24 {
        arg_a: IntermediateValue, // vectorized pointer, of size 2 (2 first inputs)
        arg_b: IntermediateValue, // vectorized pointer, of size 1 (3rd = last input)
        res: IntermediateValue,   // vectorized pointer, of size 1 (3rd = last output)
    },
    DotProduct {
        arg0: IntermediateValue, // vectorized pointer
        arg1: IntermediateValue, // vectorized pointer
        res: IntermediateValue,  // vectorized pointer
        size: ConstExpression,
    },
    MultilinearEval {
        coeffs: IntermediateValue, // vectorized pointer, chunk size = 2^n_vars
        point: IntermediateValue,  // vectorized pointer, of size `n_vars`
        res: IntermediateValue,    // vectorized pointer, of size 1
        n_vars: ConstExpression,
    },
    // HINTS (does not appears in the final bytecode)
    Inverse {
        // If the value is zero, it will return zero.
        arg: IntermediateValue, // the value to invert
        res_offset: usize,      // m[fp + res_offset] will contain the result
    },
    RequestMemory {
        offset: ConstExpression, // m[fp + offset] where the hint will be stored
        size: IntermediateValue, // the hint
        vectorized: bool, // if true, will be 8-alligned, and the returned pointer will be "divied" by 8 (i.e. everything is in chunks of 8 field elements)
    },
    DecomposeBits {
        res_offset: usize, // m[fp + res_offset..fp + res_offset + 31 * len(to_decompose)] will contain the decomposed bits
        to_decompose: Vec<IntermediateValue>,
    },
    CounterHint {
        res_offset: usize,
    },
    Print {
        line_info: String, // information about the line where the print occurs
        content: Vec<IntermediateValue>, // values to print
    },
    // noop, debug purpose only
    LocationReport {
        location: LocationInSourceCode,
    },
}

impl IntermediateInstruction {
    pub fn computation(
        operation: HighLevelOperation,
        arg_a: IntermediateValue,
        arg_c: IntermediateValue,
        res: IntermediateValue,
    ) -> Self {
        match operation {
            HighLevelOperation::Add => Self::Computation {
                operation: Operation::Add,
                arg_a,
                arg_c,
                res,
            },
            HighLevelOperation::Mul => Self::Computation {
                operation: Operation::Mul,
                arg_a,
                arg_c,
                res,
            },
            HighLevelOperation::Sub => Self::Computation {
                operation: Operation::Add,
                arg_a: res,
                arg_c,
                res: arg_a,
            },
            HighLevelOperation::Div => Self::Computation {
                operation: Operation::Mul,
                arg_a: res,
                arg_c,
                res: arg_a,
            },
            HighLevelOperation::Exp | HighLevelOperation::Mod => unreachable!(),
        }
    }

    pub fn equality(left: IntermediateValue, right: IntermediateValue) -> Self {
        Self::Computation {
            operation: Operation::Add,
            arg_a: left,
            arg_c: IntermediateValue::Constant(ConstExpression::zero()),
            res: right,
        }
    }
}

impl Display for IntermediateValue {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            IntermediateValue::Constant(value) => write!(f, "{}", value),
            IntermediateValue::Fp => write!(f, "fp"),
            IntermediateValue::MemoryAfterFp { offset } => {
                write!(f, "m[fp + {}]", offset)
            }
        }
    }
}

impl Display for IntermediaryMemOrFpOrConstant {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MemoryAfterFp { offset } => write!(f, "m[fp + {}]", offset),
            Self::Fp => write!(f, "fp"),
            Self::Constant(c) => write!(f, "{}", c),
        }
    }
}

impl Display for IntermediateInstruction {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Deref {
                shift_0,
                shift_1,
                res,
            } => write!(f, "{} = m[m[fp + {}] + {}]", res, shift_0, shift_1),
            Self::DotProduct {
                arg0,
                arg1,
                res,
                size,
            } => write!(f, "dot_product({}, {}, {}, {})", arg0, arg1, res, size),
            Self::MultilinearEval {
                coeffs,
                point,
                res,
                n_vars,
            } => write!(
                f,
                "multilinear_eval({}, {}, {}, {})",
                coeffs, point, res, n_vars
            ),
            Self::DecomposeBits {
                res_offset,
                to_decompose,
            } => {
                write!(f, "m[fp + {}..] = decompose_bits(", res_offset)?;
                for (i, expr) in to_decompose.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", expr)?;
                }
                write!(f, ")")
            }
            Self::CounterHint { res_offset } => {
                write!(f, "m[fp + {}] = counter_hint()", res_offset)
            }
            Self::Computation {
                operation,
                arg_a,
                arg_c,
                res,
            } => {
                write!(f, "{} = {} {} {}", res, arg_a, operation, arg_c)
            }
            Self::Panic => write!(f, "panic"),
            Self::Jump { dest, updated_fp } => {
                if let Some(fp) = updated_fp {
                    write!(f, "jump {} with fp = {}", dest, fp)
                } else {
                    write!(f, "jump {}", dest)
                }
            }
            Self::JumpIfNotZero {
                condition,
                dest,
                updated_fp,
            } => {
                if let Some(fp) = updated_fp {
                    write!(
                        f,
                        "jump_if_not_zero {} to {} with fp = {}",
                        condition, dest, fp
                    )
                } else {
                    write!(f, "jump_if_not_zero {} to {}", condition, dest)
                }
            }
            Self::Poseidon2_16 { arg_a, arg_b, res } => {
                write!(f, "{} = poseidon2_16({}, {})", res, arg_a, arg_b)
            }
            Self::Poseidon2_24 { arg_a, arg_b, res } => {
                write!(f, "{} = poseidon2_24({}, {})", res, arg_a, arg_b)
            }
            Self::Inverse { arg, res_offset } => {
                write!(f, "m[fp + {}] = inverse({})", res_offset, arg)
            }
            Self::RequestMemory {
                offset,
                size,
                vectorized,
            } => write!(
                f,
                "m[fp + {}] = {}({})",
                offset,
                if *vectorized { "malloc_vec" } else { "malloc" },
                size
            ),
            Self::Print { line_info, content } => {
                write!(f, "print {}: ", line_info)?;
                for (i, c) in content.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", c)?;
                }
                Ok(())
            }
            Self::LocationReport { .. } => Ok(()),
        }
    }
}

impl Display for HighLevelOperation {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            HighLevelOperation::Add => write!(f, "+"),
            HighLevelOperation::Mul => write!(f, "*"),
            HighLevelOperation::Sub => write!(f, "-"),
            HighLevelOperation::Div => write!(f, "/"),
            HighLevelOperation::Exp => write!(f, "**"),
            HighLevelOperation::Mod => write!(f, "%"),
        }
    }
}

impl Display for IntermediateBytecode {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        for (label, instructions) in &self.bytecode {
            writeln!(f, "\n{}:", label)?;
            for instruction in instructions {
                writeln!(f, "  {}", instruction)?;
            }
        }
        for (i, match_blocks) in self.match_blocks.iter().enumerate() {
            writeln!(f, "\nMatch {}:", i)?;
            for (j, case) in match_blocks.iter().enumerate() {
                writeln!(f, "  Case {}:", j)?;
                for instruction in case {
                    writeln!(f, "    {}", instruction)?;
                }
            }
        }
        writeln!(f, "\nMemory size per function:")?;
        for (function_name, size) in &self.memory_size_per_function {
            writeln!(f, "{}: {}", function_name, size)?;
        }
        Ok(())
    }
}
