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
variable, and `t` must be a literal (e.g. `range_check(x, 100)` is valid, but
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
