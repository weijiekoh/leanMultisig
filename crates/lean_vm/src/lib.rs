//! Lean VM - A minimal virtual machine implementation

pub mod core;
pub mod diagnostics;
pub mod execution;
pub mod isa;
pub mod witness;

/// Location in source code (line number)
pub type LocationInSourceCode = usize;

pub use core::*;
pub use diagnostics::*;
pub use execution::*;
pub use isa::*;
pub use witness::*;
