<!--
Copyright (c) 2026 Eduard Tykhoniuk.
SPDX-License-Identifier: CC-BY-SA-4.0
-->

# EFX prover

This repository contains code and notes for checking full EFX existence for fixed
numbers of agents and goods under additive valuations. The main prover builds a
single Z3 query over linear real arithmetic: `unsat` means no counterexample
profile exists for the requested instance size, while `sat` prints a rational
counterexample profile.

## Repository layout

- `main.cpp` - main Z3-based prover.
- `common.cpp` - ordered non-empty partition generation shared by the C++ tools.
- `run-cpp.sh` - convenience wrapper for compiling and running a C++ source file.
- `main.py` - initial Python/Z3 prototype for `N=4, M=6`.
- `check.py` - small standalone checker/prototype code.
- `soplex-prover.cpp`, `working.cpp` - alternative prover experiments.
- `tex/` - report source, bibliography, Makefile, and generated PDF.
- `proofs/` - retained machine-verification/proof artifacts.
- `logs/` - retained solver run logs.
- `experiments/` - historical experiment scripts/results; these files are kept
  as-is.

## Build and run

The C++ prover requires a compiler with C++23 support, Z3 development headers,
and `libz3`.

```sh
./run-cpp.sh main.cpp 4 8
```

The first argument is the source file to compile. The remaining arguments are
passed to the compiled program:

- `N` - number of agents.
- `M` - number of goods.

The prover currently enumerates ordered partitions into non-empty bundles, so it
requires `M >= N`.

`main.cpp` writes an SMT-LIB2 query to `proofs/problem_N_M.smt2` and then calls
Z3:

- `unsat` / `No counterexample` means every positive additive profile for that
  fixed `N,M` has a full EFX allocation within the encoded allocation family.
- `sat` / `Counterexample found` prints a model, i.e. a valuation matrix.
- `unknown` is inconclusive.

`USE_SYMMETRY` at the top of `main.cpp` controls the goods-relabelling symmetry
break. When enabled, the first agent's valuations are sorted, which substantially
reduces runtime.

## Report

Build the PDF from `tex/`:

```sh
cd tex
make
```

This requires a TeX distribution with `pdflatex` and `biber`.

## License

Code is licensed under the GNU General Public License v3.0 or later; see
`LICENSE`.

Report prose and documentation are licensed under Creative Commons
Attribution-ShareAlike 4.0 International (CC BY-SA 4.0); see
`LICENSES/CC-BY-SA-4.0.txt`. Source-code listings embedded in the report keep the
license stated in the corresponding source files.
