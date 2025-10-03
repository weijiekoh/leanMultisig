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

TODO: update this section - we may need 4 or 5 instructions instead of 3, as we
may need to set m[fp + i] and m[fp + k] to 0, depending on whether m[m[fp + x]]
and/or m[m[fp + j]] are defined.
