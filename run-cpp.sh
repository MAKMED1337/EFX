set -ex

ccache g++ "$1" -o "out/$1.x" -std=c++23 \
    -Ofast -fwhole-program -flto -march=native \
    -pipe \
    -lz3 -pthread

time ./"out/$1.x"

