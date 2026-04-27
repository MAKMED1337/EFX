#include "common.cpp"
#include <algorithm>
#include <fstream>
#include <iostream>
#include <ostream>
#include <sstream>
#include <string>
#include <thread>
#include <vector>
#include <z3++.h>

const int N = 4; // number of agents
const int M = 8; // number of items

// Encode the envy-freeness condition for a given partition.
// Returns a Z3 Boolean expression that is true iff the partition is envy-free
// under the current weight variables w[i][j] (agent i's valuation for item j).
z3::expr nonenvy(z3::context &ctx, const std::vector<std::vector<int>> &partition,
                 const std::vector<std::vector<z3::expr>> &w) {
    z3::expr_vector constraints(ctx);
    for (int i = 0; i < N; ++i) {
        // Total value of agent i's own bundle.
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

            // Total value of agent j's bundle according to i's valuations.
            z3::expr other = ctx.real_val(0);
            for (int k : partition[j]) {
                other = other + w[i][k];
            }

            // For every item k in j's bundle, agent i should not envy j
            // after removing that item from j's bundle.
            for (int k : partition[j]) {
                constraints.push_back(total >= other - w[i][k]);
            }
        }
    }
    return z3::mk_and(constraints);
}

struct Variable {
    std::string name;
    std::vector<int> indices;
};

Variable parse_variable_name(std::string const &name) {
    std::istringstream ss(name);
    std::vector<std::string> tokens;
    std::string token;
    while (getline(ss, token, '_')) {
        tokens.push_back(token);
    }

    std::vector<int> indices;
    for (int i = 1; i < tokens.size(); i++) {
        indices.push_back(stoi(tokens[i]));
    }
    return Variable{tokens[0], indices};
}

void print_frac(z3::expr f) { std::cout << f.numerator() << "/" << f.denominator() << " "; }

void print(z3::model m) {
    using namespace std;
    using namespace z3;
    vector<vector<expr>> values(N, vector<expr>(M, expr(m.ctx())));
    for (unsigned i = 0; i < m.size(); ++i) {
        func_decl v = m[i];
        auto name = v.name().str();
        auto var = parse_variable_name(name);
        auto value = m.get_const_interp(v);

        if (var.name == "w") {
            assert(var.indices.size() == 2);
            values[var.indices[0]][var.indices[1]] = value;
        } else {
            assert(false);
        }
    }

    for (int ind = 0; ind < values.size(); ind++) {
        auto i = values[ind];
        for (auto j : i) {
            print_frac(j);
        }
        cout << "\n";
    }
}

z3::solver get_solver(z3::context &ctx) {
    z3::tactic simplify = z3::tactic(ctx, "simplify");
    z3::tactic solve_eqs = z3::tactic(ctx, "solve-eqs");
    z3::tactic blast_ite = z3::tactic(ctx, "blast-term-ite");
    z3::tactic propagate = z3::tactic(ctx, "propagate-values");
    z3::tactic smtt = z3::tactic(ctx, "smt");

    // Combine them into a sequence
    z3::tactic t = simplify & solve_eqs & blast_ite & propagate & smtt;
    return t.mk_solver();

    // z3::solver solver = z3::solver(ctx);
}

int main() {
    // Enable proof generation globally.
    z3::set_param("proof", "true");

    z3::context ctx;
    z3::solver solver = get_solver(ctx);

    std::cout << "N=" << N << " M=" << M << std::endl;
    unsigned threads = std::max(1u, std::thread::hardware_concurrency());
    std::cout << "Available hardware threads: " << threads << "\n";

    // Create weight variables.
    std::vector<std::vector<z3::expr>> w(N, std::vector<z3::expr>(M, z3::expr(ctx)));
    for (int i = 0; i < N; ++i) {
        for (int j = 0; j < M; ++j) {
            std::string name = "w_" + std::to_string(i) + "_" + std::to_string(j);
            w[i][j] = ctx.real_const(name.c_str());
        }
    }

    // Positivity.
    for (int i = 0; i < N; ++i) {
        for (int j = 0; j < M; ++j) {
            solver.add(w[i][j] > 0);
        }
    }

    // First agent's weights sorted.
    for (int j = 0; j < M - 1; ++j) {
        solver.add(w[0][j] <= w[0][j + 1]);
    }

    // Generate partitions.
    auto partitions = ordered_groups(N, M);
    std::cout << "Number of partitions = " << partitions.size() << std::endl;

    // Build the disjunction.
    z3::expr_vector valid_exprs(ctx);
    int count = 0;
    for (const auto &part : partitions) {
        valid_exprs.push_back(nonenvy(ctx, part, w));
    }
    z3::expr or_valid = z3::mk_or(valid_exprs);
    solver.add(!or_valid);

    // Export SMT‑LIB2 for external verification.
    std::string smt_name = "proofs/problem_" + std::to_string(N) + "_" + std::to_string(M) + ".smt2";
    std::ofstream smt(smt_name);
    smt << solver.to_smt2() << std::endl;
    smt.close();
    std::cout << "SMT‑LIB2 script saved to " << smt_name << std::endl;

    std::cout << "Solving..." << std::endl;
    z3::check_result result = solver.check();

    if (result == z3::unsat) {
        std::cout << "No counterexample :(" << std::endl;
        // Attempt to get proof (may throw if Z3 doesn't support it for LRA).
        z3::expr proof = solver.proof();
        std::string proof_name = "proofs/proof_" + std::to_string(N) + "_" + std::to_string(M) + ".z3";
        std::ofstream proof_file(proof_name);
        proof_file << proof << std::endl;
        proof_file.close();
        std::cout << "Proof saved to " << proof_name << std::endl;
    } else if (result == z3::sat) {
        std::cout << "Counterexample found:" << std::endl;
        z3::model m = solver.get_model();
        std::cout << m << std::endl;
        print(m);
    } else {
        std::cout << "Unknown result:" << result << std::endl;
    }

    return 0;
}
