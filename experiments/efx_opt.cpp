// Optimization sweep on top of the best normalization (norm4 = w[i][0] embedded
// as constant 1). Experiment code only; does NOT touch main.cpp.
//
// Env levers (all optional):
//   N, M, USE_SYMMETRY, NORMALIZE   - as in efx_exp.cpp (default NORMALIZE=4)
//   ARITH=<n>     -> z3::set_param("smt.arith.solver", n)   (e.g. 2 simplex, 6 new)
//   PARALLEL=1    -> z3::set_param("parallel.enable", true)
//   THREADS=<n>   -> z3::set_param("parallel.threads.max", n)
//   TACTIC=1      -> solve via simplify & solve-eqs & propagate-values & smt
//   ROW0MIN=1     -> for the sorted agent 0, emit only the binding (min-value)
//                    EFX constraint per opponent bundle instead of one per item
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

// EFX condition for a partition. When row0_min is set, agent 0's row is sorted
// ascending (symmetry break) so within any opponent bundle the smallest-index
// item has the smallest value to agent 0 -> it is the only binding good, and the
// AND over all goods reduces to that single constraint (sound, equivalent).
z3::expr nonenvy(z3::context &ctx, const int N, const std::vector<std::vector<int>> &partition,
                 const std::vector<std::vector<z3::expr>> &w, bool row0_min) {
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

            if (row0_min && i == 0) {
                // partition[j] is sorted ascending; w[0][*] sorted ascending too,
                // so partition[j].front() is the min-value good for agent 0.
                int k = partition[j].front();
                constraints.push_back(total >= other - w[0][k]);
            } else {
                for (int k : partition[j]) {
                    constraints.push_back(total >= other - w[i][k]);
                }
            }
        }
    }
    return z3::mk_and(constraints);
}

int main() {
    const int N = env_int("N", 4);
    const int M = env_int("M", 8);
    const bool USE_SYMMETRY = env_int("USE_SYMMETRY", 1) != 0;
    const int NORMALIZE = env_int("NORMALIZE", 4);
    const int ARITH = env_int("ARITH", -1);
    const bool PARALLEL = env_int("PARALLEL", 0) != 0;
    const int THREADS = env_int("THREADS", 0);
    const bool TACTIC = env_int("TACTIC", 0) != 0;
    const bool ROW0MIN = env_int("ROW0MIN", 0) != 0;

    // Global Z3 params must be set before the context is created.
    if (ARITH >= 0) {
        z3::set_param("smt.arith.solver", ARITH);
    }
    if (PARALLEL) {
        z3::set_param("parallel.enable", true);
    }
    if (THREADS > 0) {
        z3::set_param("parallel.threads.max", THREADS);
    }

    z3::context ctx;

    z3::solver solver = TACTIC ? (z3::tactic(ctx, "simplify") & z3::tactic(ctx, "solve-eqs") &
                                  z3::tactic(ctx, "propagate-values") & z3::tactic(ctx, "smt"))
                                     .mk_solver()
                               : z3::solver(ctx);
    // TIMEOUT_MS=0 (default) means no cap; otherwise cap in milliseconds.
    const unsigned timeout_ms = static_cast<unsigned>(env_int("TIMEOUT_MS", 0));
    if (timeout_ms > 0) {
        solver.set("timeout", timeout_ms);
    }

    std::cerr << "N=" << N << " M=" << M << " sym=" << USE_SYMMETRY << " norm=" << NORMALIZE
              << " arith=" << ARITH << " parallel=" << PARALLEL << " threads=" << THREADS
              << " tactic=" << TACTIC << " row0min=" << ROW0MIN << std::endl;

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

    for (int i = 0; i < N; ++i) {
        for (int j = 0; j < M; ++j) {
            if (NORMALIZE == 4 && j == 0) {
                continue;
            }
            solver.add(w[i][j] > 0);
        }
    }

    if (USE_SYMMETRY) {
        for (int j = 0; j < M - 1; ++j) {
            solver.add(w[0][j] <= w[0][j + 1]);
        }
    }

    if (NORMALIZE == 1 || NORMALIZE == 2) {
        solver.add(w[0][0] == 1);
    }
    if (NORMALIZE == 3) {
        for (int i = 0; i < N; ++i) {
            solver.add(w[i][0] == 1);
        }
    }
    if (NORMALIZE == 1) {
        for (int i = 1; i < N; ++i) {
            z3::expr s = ctx.real_val(0);
            for (int j = 0; j < M; ++j) {
                s = s + w[i][j];
            }
            solver.add(s == 1);
        }
    }

    // ROW0MIN requires agent 0 to actually be sorted.
    const bool row0_min = ROW0MIN && USE_SYMMETRY;

    auto partitions = ordered_groups(N, M);
    std::cerr << "partitions=" << partitions.size() << std::endl;

    z3::expr_vector valid_exprs(ctx);
    for (const auto &part : partitions) {
        valid_exprs.push_back(nonenvy(ctx, N, part, w, row0_min));
    }
    solver.add(!z3::mk_or(valid_exprs));

    std::cerr << "solving..." << std::endl;
    auto t0 = std::chrono::steady_clock::now();
    z3::check_result result = solver.check();
    auto t1 = std::chrono::steady_clock::now();
    double seconds = std::chrono::duration<double>(t1 - t0).count();

    std::string res = result == z3::unsat ? "unsat" : result == z3::sat ? "sat" : "unknown";

    std::cout << "RESULT N=" << N << " M=" << M << " norm=" << NORMALIZE << " arith=" << ARITH
              << " parallel=" << PARALLEL << " threads=" << THREADS << " tactic=" << TACTIC
              << " row0min=" << row0_min << " result=" << res << " seconds=" << seconds << std::endl;
    return 0;
}
