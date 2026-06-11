#!/usr/bin/env bash
# Sweep the promising levers on the two hard configs (N=3 M=7, N=4 M=7),
# all on top of NORMALIZE=4. Sequential. Appends RESULT lines to raw_opt.txt.
set -eu
cd "$(dirname "$0")"
RAW=raw_opt.txt
: > "$RAW"

emit() {
    local tag="$1"; shift
    echo "=== $tag ==="
    local line
    line=$("$@" ./efx_opt.x)
    echo "$line"
    echo "$tag | $line" >> "$RAW"
}

for nm in "3 7" "4 7"; do
    read -r n m <<< "$nm"
    base="env N=$n M=$m NORMALIZE=4 USE_SYMMETRY=1"
    emit "N=$n M=$m baseline(norm4)"        $base
    emit "N=$n M=$m arith2"                 $base ARITH=2
    emit "N=$n M=$m arith2+row0min"         $base ARITH=2 ROW0MIN=1
    emit "N=$n M=$m row0min"                $base ROW0MIN=1
    emit "N=$n M=$m parallel"               $base PARALLEL=1
done
echo "done -> $RAW"
