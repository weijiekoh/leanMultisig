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

## Memory hints

The hard part is knowing what to store in `m[m[fp + x]]` and `m[m[fp + j]]`. We
need to store the values already in those cells, as said cells could already be
in use. Unfortunately, their contents cannot be known during compile-time, so
the prover needs do extra work.

e.g. if `m[m[fp + x]] = 123`, we need to set `m[fp + i]` to 123, so that in step
1, when we set `m[m[fp + x]]` to `m[fp + i]`, 
we won't change the value of `m[m[fp + x]]` which could already be in use.

// We want to check that val < t
// But there is already data in m[val]
Possibilities
  - v < 64
    - m[v] is already initialised, so the deref will work
  - v == 64
    - m[64] is uninitialised, and some instructions are needed to initialise m[64]
  - v > 64

Where 64 is the length of the public memory initialised before execution.


## Flowchart

Initial state:
    - m[fp + x] contains val
    - m[fp + y] contains t

Step 1: m[fp + i] = m[m[fp + x]] using deref
    - Key idea: m[val] will OOM if val >= M

m[val] is already initialised?
    - Y:
    - N:
