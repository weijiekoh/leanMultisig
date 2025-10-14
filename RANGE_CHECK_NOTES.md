# The range-check technique

According to section 2.5.3 of `minimal_zkVM.pdf`, we can achieve a range check using 3 cycles.

This technique allows us to check that some memory cell is smaller than some
value `t`, where `t <= 2^16` and `M <= 2^29 < p / 2`.

NOTE: we should clarify if `t <= 2^16` even if `M >= 2^16`.

The technique is as such.

Let `m[fp + x]` be the memory cell we want to range-check.

Let `m[fp + i]`, `m[fp + j]`, and `m[fp + k]` be auxiliary memory cells that
have not been used yet.

The three steps are:

1. Using DEREF, set `m[fp + i]` to `m[m[fp + x]]`.
    - Since this will fail if `m[fp + x] >= M`, we ensure that `m[fp + x] < M`.

2. Using ADD, ensure (via constraint-solving): `m[fp + j] + m[m[fp + x]] = (t - 1)`.

3. Using DEREF, ensure `m[m[fp + j]] = m[fp + k]`.
    - Since this will fail if `m[fp + j] >= M`, we ensure that `(t - 1) - m[fp + x] < M`.

Now that we have ensured that:

- `m[fp + x] < M`
- `(t - 1) - m[fp + x] < M`

Recall that `t <= 2^16` and `M <= 2^29 < p / 2`. This gives us `m[fp + x] < t`.

## Implementation

### `range_check()` keyword and hint

We introduce a new language keyword: `range_check(v, t)`, where `v` must be a
variable, and `t` must be a constant (e.g. `range_check(x, 100)` is valid, but
`range_check(x, y)` is not).

The compiler will treat `range_check()` as a hint. It will insert 3-step
range-check opcodes at the end of execution (right before the opcode with PC
`bytecode.ending_pc`), and update `bytecode.ending_pc` accordingly. This is
necessary because it is too complex to insert these opcodes in-place without
first executing the bytecode to determine which memory locations will and will
not be set so as to determine correct `i`, `j`, and `k` values per range check.
To complicate matters, the way the compiler sets up JUMP destinations in memory
may conflict with these auxiliary memory cells. Finally, this approach is more
auditble and less complex.

### Linking the hints to the 3-step range-check opcodes

It is necessary to affix metadata to each `range_check` hint to indicate which
set of 3 opcodes will implement it. This is to make it clear that if one of the
3 opcodes fails, the programmer can determine which range check failed.

## Current Implementation Analysis

### Changes Made Since Commit 43205ce23924c05183174fc1b698f55e0265f64f

The current codebase has been significantly modified to support range checks,
but the implementation **deviates from the approach described above** and has
critical issues.

#### **Categories of Changes**

**1. Range Check Compilation Implementation**
- `RANGE_CHECK_NOTES.md` - This documentation file
- `crates/lean_compiler/src/lang.rs` - Added `RangeCheck` AST node (ok)
- `crates/lean_compiler/src/grammar.pest` - Added `range_check_statement` grammar rule (ok)
- `crates/lean_compiler/src/parser.rs` - Added range check parsing (ok)
- `crates/lean_compiler/src/a_simplify_lang.rs` - Added range check simplification (ok?)
- `crates/lean_compiler/src/b_compile_intermediate.rs` - Added range check intermediate compilation (ok)
- `crates/lean_compiler/src/c_compile_final.rs` - Added range check final compilation (ok)
- `crates/lean_compiler/src/intermediate_bytecode.rs` - Added intermediate range check instruction
- `crates/lean_compiler/src/lib.rs` - Added range check compilation orchestration (ok)
- `crates/lean_vm/src/lean_isa.rs` - Added `RangeCheck` instruction variant
- `crates/lean_vm/src/runner.rs` - Added massive `compile_range_checks()` function (lines ~157-478) (ok)
- `crates/lean_compiler/tests/test_range_check.rs` - New test file with range check test cases

**2. VM Runner State Representation Refactor**
- `crates/lean_vm/src/runner.rs` - Major refactor:
  - Added `ExecutionResult` struct to track execution state
  - Added `memory_write_history` tracking throughout execution
  - Refactored `execute_bytecode()` to do two-pass execution
  - Added numerous helper functions for memory management
  - Enhanced instruction execution with memory tracking
- `crates/lean_vm/src/memory.rs` - Added debug printing for memory operations
- `crates/lean_vm/src/lib.rs` - Updated exports

**3. Instruction and Hint Executor Changes**
- `crates/lean_vm/src/runner.rs` - Enhanced `execute_instruction()` with:
  - Memory write history tracking for all instructions
  - Updated Poseidon operations with proper memory tracking
  - Updated dot product and multilinear eval operations
- `crates/lean_prover/witness_generation/src/instruction_encoder.rs` - Added range check encoding
- `crates/lean_prover/src/prove_execution.rs` - Updated to handle mutable bytecode

**4. Documentation and Notes**
- `CLAUDE.md` - New file with extensive codebase documentation

#### **Critical Issue: Implementation Violates Design Principles**

**Current approach:** The implementation replaces range checks **in-place** during compilation using `compile_range_checks()`, causing PC/jump address conflicts.

**Documented approach (above):** Should insert range check opcodes **at the end** before `bytecode.ending_pc`.

**Root cause of current failures:**
1. **Auxiliary variable conflicts**: Range check auxiliary variables (`i`, `j`, `k`) conflict with function call stack locations and return addresses
2. **PC reuse**: The same PC numbers are reused for different range check expansions, breaking jump destinations
3. **Control flow corruption**: Function returns jump to wrong addresses because the jump table assumes original PC numbering

**Example failure from test output:**
```
Memory address 0 is already set to 0, and cannot be set to 73
```
This occurs because:
- `m[73]` stores return address `8` for function calls
- Range check compilation tries to use nearby memory locations
- The deref instruction attempts to write to `m[0]` which conflicts with initial memory

#### **Required Fix**

The implementation must be rewritten to follow the documented approach:

1. **Do NOT replace range checks in-place**
2. **Append range check opcodes at the end** before `bytecode.ending_pc`  
3. **Preserve original control flow** - no PC renumbering
4. **Use truly unused memory locations** for auxiliary variables
5. **Add metadata linking** each range check to its 3-step implementation

This approach avoids all control flow conflicts and makes range check failures easily traceable to their source.
