#!/usr/bin/env bash
# Benchmark base vs normalized EFX prover over a small (N,M) grid.
# Each run is capped at 10 min by the solver's internal timeout.
set -eu

cd "$(dirname "$0")"

BIN=efx_exp.x
RESULTS=results.md

echo "Building $BIN ..."
ccache g++ efx_exp.cpp -o "$BIN" -std=c++23 \
    -Ofast -fwhole-program -flto -march=native \
    -pipe \
    -lz3 -pthread

# Grid: N=3 (M=5,6,7), N=4 (M=6,7); each base (NORMALIZE=0) and normalized (=1).
CONFIGS=(
    "3 5"
    "3 6"
    "3 7"
    "4 6"
    "4 7"
)

RAW=raw_results.txt
: > "$RAW"

for cfg in "${CONFIGS[@]}"; do
    read -r n m <<< "$cfg"
    for norm in 0 1; do
        echo "=== N=$n M=$m NORMALIZE=$norm ==="
        line=$(N=$n M=$m USE_SYMMETRY=1 NORMALIZE=$norm ./"$BIN")
        echo "$line"
        echo "$line" >> "$RAW"
    done
done

echo
echo "Raw results saved to $RAW"
echo "Now run build the markdown table from $RAW (done by the agent)."
