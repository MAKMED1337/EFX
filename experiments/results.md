# EFX prover: per-agent normalization experiment

Question: does pinning the per-agent scale "gauge freedom" speed up the Z3 LRA
prover? Each agent's EFX constraints are homogeneous degree-1 in that agent's own
row `w[i][*]`, so independent positive per-row scaling preserves `sat`/`unsat`.
We can therefore add a normalization per row for free (soundness-wise) and see if
it helps Z3.

All runs: `USE_SYMMETRY=1` (agent 0's row sorted ascending), solver timeout 600s,
`-Ofast -march=native`, single binary `efx_exp.cpp` driven by env vars, run
sequentially (no CPU contention).

Schemes:
- **base** (`NORMALIZE=0`): no normalization (matches the real `main.cpp`).
- **norm1** (`=1`): `w[0][0]=1` **and** rows `i>=1` sum to 1.
- **norm2** (`=2`): `w[0][0]=1` only.
- **norm3** (`=3`): `w[i][0]=1` for **every** row (constraint form; vars still created).
- **norm4** (`=4`): `w[i][0]` **embedded as the literal 1** — those N variables
  are never created, solver sees only `N·(M-1)` reals.

## Solve time (seconds), all `unsat`

| N | M | base | norm1 (w00+sum) | norm2 (w00 only) | norm3 (wi0=1) | norm4 (wi0 embedded) |
|---|---|------|-----------------|------------------|---------------|----------------------|
| 3 | 5 |   0.019 |   0.049 |   0.015 |   0.010 |   0.011 |
| 3 | 6 |   1.335 |   4.776 |   1.434 |   0.847 |   1.175 |
| 3 | 7 | 137.535 | 422.703 | 137.781 |  62.944 |  56.216 |
| 4 | 6 |   0.629 |   1.233 |   0.502 |   0.366 |   0.461 |
| 4 | 7 | 174.692 | 294.043 | 353.255 | 190.725 | 159.043 |

Every scheme returned **unsat** for every config — the per-row-scaling soundness
argument holds (normalization never changed the answer).

## Speedup vs base (base / variant; >1 = faster)

| N | M | norm1 | norm2 | norm3 | norm4 |
|---|---|-------|-------|-------|-------|
| 3 | 5 | 0.38 | 1.24 | 1.89 | 1.70 |
| 3 | 6 | 0.28 | 0.93 | 1.58 | 1.14 |
| 3 | 7 | 0.33 | 1.00 | 2.19 | 2.45 |
| 4 | 6 | 0.51 | 1.25 | 1.72 | 1.36 |
| 4 | 7 | 0.59 | 0.49 | 0.92 | 1.10 |

## Conclusion

Pinning the **first coordinate of every row** (norm3/norm4) is the first scheme
that actually helps — and the **embedded form (norm4) is the winner**: faster
than base on *all* five configs, including both hard ones (N=3 M=7: 2.45×; N=4
M=7: 1.10×). The earlier failures are now explained:

- **norm1** (sum=1) was always 1.7–3.6× slower: the `sum=1` equalities couple
  every variable in a row and drag fractions through the simplex.
- **norm2** (pin only row 0) was neutral-to-worse: fixing one row's scale leaves
  the other N−1 scale rays free, so it doesn't really cut the search.
- **norm3** (pin every row, constraint form) is faster on 4/5 configs (up to
  2.2×) but very slightly slower on the hardest N=4 M=7 — the pinned variables
  still exist and Z3 spends effort eliminating them.
- **norm4** (embed the 1, never create the variable) dominates: it removes N
  variables outright, so it's strictly the smaller model. It beats both base and
  norm3 on the two M=7 cases (159s vs 175s/191s; 56s vs 138s/63s).

What mattered was **cutting all N scale degrees of freedom at once and doing it
by shrinking the model, not by adding constraints.**

### Recommendation
The embedded `w[i][0]=1` normalization is a sound, free win and is the approach
to carry to the real prover. Concretely, in `main.cpp` build `w[i][0]` as
`ctx.real_val(1)` instead of `ctx.real_const(...)` and skip its positivity
constraint — `nonenvy` needs no change. (Left to the user per "don't touch
`main.cpp`".) Worth retrying the open N=4 M=8 case with norm4 given the ~1.1–2.5×
speedups on the hardest measured instances.

---

# Round 4: other optimizations (on top of norm4)

Levers tested (`experiments/efx_opt.cpp`, env-driven), all on top of norm4:
- **`ARITH=2`** — `smt.arith.solver=2`, Z3's older Simplex-based arithmetic
  engine (the default for QF_LRA here picks a different one).
- **`PARALLEL=1`** — `parallel.enable=true` (machine has 144 threads).
- **`TACTIC=1`** — preprocess via `simplify & solve-eqs & propagate-values & smt`.
- **`ROW0MIN=1`** — algorithmic: agent 0's row is sorted, so within an opponent
  bundle the smallest-index good is the only binding EFX good; emit one
  constraint instead of one per good (sound, equivalent).

## Sweep on the two hard configs (norm4 baseline, seconds)

| config | norm4 base | arith2 | arith2+row0min | row0min | parallel |
|--------|-----------:|-------:|---------------:|--------:|---------:|
| N=3 M=7 |  56.1 | 21.0 | 16.9 |  65.8 | 106.4 |
| N=4 M=7 | 157.5 | 98.5 | 138.5 | 222.0 | **600 (timeout)** |

- **`arith2` is the robust winner** (1.6–2.7× over norm4). **`parallel` is
  catastrophic** — it timed out N=4 M=7 (>600s vs 157s). `tactic` was negligible.
  `row0min` is **inconsistent**: it helped N=3 M=7 but hurt N=4 M=7 — the smaller
  constraint set changes Z3's search path unpredictably, so it's not a reliable
  win. Drop parallel, tactic, and row0min.

## Winning combo `norm4 + arith2`, full grid (seconds, all `unsat`)

| N | M | original base | norm4 | **norm4 + arith2** | speedup vs base |
|---|---|--------------:|------:|-------------------:|----------------:|
| 3 | 5 |   0.019 |   0.011 |   0.0069 | 2.7× |
| 3 | 6 |   1.335 |   1.175 |   0.250  | 5.3× |
| 3 | 7 | 137.535 |  56.216 |  20.875  | **6.6×** |
| 4 | 6 |   0.629 |   0.461 |   0.138  | 4.6× |
| 4 | 7 | 174.692 | 159.043 |  95.549  | 1.8× |

## Recommendation (updated)

Use **embedded `w[i][0]=1` (norm4) + `smt.arith.solver=2`** together — sound,
no change to `nonenvy`, and 1.8–6.6× faster than the current base across the
grid. In `main.cpp`: call `z3::set_param("smt.arith.solver", 2)` (or
`solver.set` with that param) and build column 0 as `ctx.real_val(1)`. Do **not**
enable Z3 parallel mode — it badly hurts this workload. This is the configuration
to try on the open N=4 M=8 case.

