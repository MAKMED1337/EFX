To run `.cpp` files use `./run-cpp.sh {NAME}`. The main file is `main.cpp` it contains z3 proover for EFX problem with $N$ people and $M$ items, they can be modified inside the code. After it finished it will generate a z3 proof inside the `proofs/` directory and print its name.

Toggles at the top of `main.cpp`:

- `N`, `M` — number of agents and goods.
- `USE_SYMMETRY` — if `true`, adds the goods-relabelling symmetry break (sorts agent 0's valuations); set to `false` to run the unsorted version, which is much slower but lets others verify the result without that optimisation.

`main.py` is an initial Python prototype (N=4, M=6) using the Z3 bindings; it does not apply the symmetry break, so it doubles as an unsorted cross-check.
