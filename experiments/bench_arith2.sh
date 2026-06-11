#!/usr/bin/env bash
# Validate the winning combo (NORMALIZE=4 embedded + smt.arith.solver=2) across
# the full grid. Sequential. Appends to raw_arith2.txt.
set -eu
cd "$(dirname "$0")"
RAW=raw_arith2.txt
: > "$RAW"
for nm in "3 5" "3 6" "3 7" "4 6" "4 7"; do
    read -r n m <<< "$nm"
    echo "=== N=$n M=$m norm4+arith2 ==="
    line=$(N=$n M=$m NORMALIZE=4 USE_SYMMETRY=1 ARITH=2 ./efx_opt.x)
    echo "$line"
    echo "$line" >> "$RAW"
done
echo "done -> $RAW"
