// Experiment copy of the EFX prover (does NOT touch main.cpp / real code).
// Reads N, M, USE_SYMMETRY, NORMALIZE from the environment so one binary can
// benchmark many configs. Normalization scheme under test:
//   row 0:      w[0][0] = 1            (pin the symmetry-sorted row's scale)
//   rows i>=1:  sum_j w[i][j] = 1      (sum-normalize the rest)
// This is sound because every constraint for agent i is homogeneous degree 1
// in row w[i][*], so independent positive per-row scaling preserves sat/unsat.
#include "../common.cpp"
#include <chrono>
#include <cstdlib>
#include <iostream>
#include <string>
#include <vector>
#include <z3++.h>

static int env_int(const char *name, int fallback) {
    const char *v = std::getenv(name);
    return v ? std::stoi(v) : fallback;
}

// Envy-freeness condition for a partition under weights w (agent i values item j
// at w[i][j]). Identical logic to main.cpp's nonenvy.
z3::expr nonenvy(z3::context &ctx, const int N, const std::vector<std::vector<int>> &partition,
                 const std::vector<std::vector<z3::expr>> &w) {
    z3::expr_vector constraints(ctx);
    for (int i = 0; i < N; ++i) {
        z3::expr total = ctx.real_val(0);
        for (int j : partition[i]) {
            total = total + w[i][j];
        }

        for (int j = 0; j < N; ++j) {
            if (i == j) {
                continue;
            }
            if (partition[j].size() <= 1) {
                continue;
            }

            z3::expr other = ctx.real_val(0);
            for (int k : partition[j]) {
                other = other + w[i][k];
            }

            for (int k : partition[j]) {
                constraints.push_back(total >= other - w[i][k]);
            }
        }
    }
    return z3::mk_and(constraints);
}

int main() {
    const int N = env_int("N", 4);
    const int M = env_int("M", 8);
    const bool USE_SYMMETRY = env_int("USE_SYMMETRY", 1) != 0;
    // NORMALIZE: 0 = none, 1 = w[0][0]=1 + rows i>=1 sum to 1, 2 = w[0][0]=1 only.
    const int NORMALIZE = env_int("NORMALIZE", 0);

    z3::context ctx;
    z3::solver solver(ctx);
    // Cap solving so an over-budget run returns `unknown` instead of hanging.
    solver.set("timeout", 600000u); // 10 minutes, in ms

    std::cerr << "N=" << N << " M=" << M << " sym=" << USE_SYMMETRY << " norm=" << NORMALIZE
              << std::endl;

    // Weight variables. In embedded mode (NORMALIZE==4) column 0 is the literal
    // constant 1 rather than a variable, so the solver never sees those N vars.
    std::vector<std::vector<z3::expr>> w(N, std::vector<z3::expr>(M, z3::expr(ctx)));
    for (int i = 0; i < N; ++i) {
        for (int j = 0; j < M; ++j) {
            if (NORMALIZE == 4 && j == 0) {
                w[i][j] = ctx.real_val(1);
                continue;
            }
            std::string name = "w_" + std::to_string(i) + "_" + std::to_string(j);
            w[i][j] = ctx.real_const(name.c_str());
        }
    }

    // Positivity (skip column 0 when embedded: it's the constant 1).
    for (int i = 0; i < N; ++i) {
        for (int j = 0; j < M; ++j) {
            if (NORMALIZE == 4 && j == 0) {
                continue;
            }
            solver.add(w[i][j] > 0);
        }
    }

    // Goods-relabelling symmetry break: agent 0's weights sorted ascending.
    if (USE_SYMMETRY) {
        for (int j = 0; j < M - 1; ++j) {
            solver.add(w[0][j] <= w[0][j + 1]);
        }
    }

    // Per-agent normalization (sound: per-row positive scaling preserves all
    // constraints).
    //   1: w[0][0]=1 and rows i>=1 sum to 1
    //   2: w[0][0]=1 only
    //   3: w[i][0]=1 for every row (constraint form)
    //   4: w[i][0] embedded as the constant 1 (handled at construction above)
    if (NORMALIZE == 1 || NORMALIZE == 2) {
        solver.add(w[0][0] == 1); // pin row 0's scale
    }
    if (NORMALIZE == 3) {
        for (int i = 0; i < N; ++i) { // pin every row's first coordinate
            solver.add(w[i][0] == 1);
        }
    }
    if (NORMALIZE == 1) {
        for (int i = 1; i < N; ++i) { // sum-normalize the remaining rows
            z3::expr s = ctx.real_val(0);
            for (int j = 0; j < M; ++j) {
                s = s + w[i][j];
            }
            solver.add(s == 1);
        }
    }

    auto partitions = ordered_groups(N, M);
    std::cerr << "partitions=" << partitions.size() << std::endl;

    z3::expr_vector valid_exprs(ctx);
    for (const auto &part : partitions) {
        valid_exprs.push_back(nonenvy(ctx, N, part, w));
    }
    solver.add(!z3::mk_or(valid_exprs));

    std::cerr << "solving..." << std::endl;
    auto t0 = std::chrono::steady_clock::now();
    z3::check_result result = solver.check();
    auto t1 = std::chrono::steady_clock::now();
    double seconds = std::chrono::duration<double>(t1 - t0).count();

    std::string res = result == z3::unsat ? "unsat" : result == z3::sat ? "sat" : "unknown";

    // Machine-readable result line on stdout.
    std::cout << "RESULT N=" << N << " M=" << M << " norm=" << NORMALIZE << " sym=" << USE_SYMMETRY
              << " result=" << res << " seconds=" << seconds << std::endl;
    return 0;
}
