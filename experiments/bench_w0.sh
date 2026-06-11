#!/usr/bin/env bash
# Benchmark w[i][0]=1 normalization, constraint form (NORMALIZE=3) and embedded
# form (NORMALIZE=4), over the same grid. Sequential to avoid CPU contention.
set -eu
cd "$(dirname "$0")"

BIN=efx_exp3.x
echo "Building $BIN ..."
ccache g++ efx_exp.cpp -o "$BIN" -std=c++23 \
    -Ofast -fwhole-program -flto -march=native \
    -pipe \
    -lz3 -pthread

CONFIGS=( "3 5" "3 6" "3 7" "4 6" "4 7" )
RAW=raw_results_w0.txt
: > "$RAW"

for norm in 3 4; do
    for cfg in "${CONFIGS[@]}"; do
        read -r n m <<< "$cfg"
        echo "=== N=$n M=$m NORMALIZE=$norm ==="
        line=$(N=$n M=$m USE_SYMMETRY=1 NORMALIZE=$norm ./"$BIN")
        echo "$line"
        echo "$line" >> "$RAW"
    done
done
echo "Raw results saved to $RAW"
