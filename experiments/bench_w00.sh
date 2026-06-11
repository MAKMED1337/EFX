#!/usr/bin/env bash
# Benchmark the w[0][0]=1-only normalization (NORMALIZE=2) over the same grid.
# Uses the prebuilt efx_exp2.x. Run after the main grid to avoid CPU contention.
set -eu
cd "$(dirname "$0")"

CONFIGS=( "3 5" "3 6" "3 7" "4 6" "4 7" )
RAW=raw_results_w00.txt
: > "$RAW"

for cfg in "${CONFIGS[@]}"; do
    read -r n m <<< "$cfg"
    echo "=== N=$n M=$m NORMALIZE=2 (w00 only) ==="
    line=$(N=$n M=$m USE_SYMMETRY=1 NORMALIZE=2 ./efx_exp2.x)
    echo "$line"
    echo "$line" >> "$RAW"
done
echo "Raw w00-only results saved to $RAW"
