#!/usr/bin/env bash

set -ex

if [ "$#" -lt 1 ]; then
    echo "Usage: $0 SOURCE.cpp [program args...]" >&2
    exit 2
fi

src="$1"
shift

mkdir -p out

ccache g++ "$src" -o "out/$src.x" -std=c++23 \
    -Ofast -fwhole-program -flto -march=native \
    -pipe \
    -lz3 -pthread

time ./"out/$src.x" "$@"
