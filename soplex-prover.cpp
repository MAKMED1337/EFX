#include "common.cpp"
#include <algorithm>
#include <array>
#include <cstdlib>
#include <iostream>
#include <mutex>
#include <optional>
#include <queue>
#include <soplex.h>
#include <soplex/spxsolver.h>
#include <syncstream>
#include <thread>
#include <vector>

using namespace std;
using namespace soplex;

constexpr int N = 4, M = 8;

using Rat = Rational;
using Lin = vector<pair<int, Rat>>;

struct ExactLP {
    SoPlex spx;
    int nextCol = 0;

    ExactLP() {
        // Exact rational mode.
        spx.setIntParam(SoPlex::READMODE, SoPlex::READMODE_RATIONAL);
        spx.setIntParam(SoPlex::SOLVEMODE, SoPlex::SOLVEMODE_RATIONAL);
        spx.setIntParam(SoPlex::CHECKMODE, SoPlex::CHECKMODE_RATIONAL);
        spx.setIntParam(SoPlex::SYNCMODE, SoPlex::SYNCMODE_AUTO);
        spx.setRealParam(SoPlex::FEASTOL, 0.0);
        spx.setRealParam(SoPlex::OPTTOL, 0.0);

        // Reduce preprocessing-related instability.
        spx.setIntParam(SoPlex::SIMPLIFIER, SoPlex::SIMPLIFIER_OFF);
        spx.setIntParam(SoPlex::SCALER, SoPlex::SCALER_OFF);

        // We maximize eps to encode strict inequalities.
        spx.setIntParam(SoPlex::OBJSENSE, SoPlex::OBJSENSE_MAXIMIZE);

        spx.setIntParam(SoPlex::VERBOSITY, 0);
    }

    int addVar(const Rat &obj = Rat(0), const Rat &lb = Rat(0), const Rat &ub = infinity) {
        DSVectorRational dummy(0);
        spx.addColRational(LPColRational(obj, dummy, ub, lb));
        return nextCol++;
    }

    void addRow(const Lin &terms, const Rat &lhs, const Rat &rhs) {
        DSVectorRational row((int)terms.size());
        for (const auto &[idx, coef] : terms) {
            row.add(idx, coef);
        }

        // SoPlex uses LPRowRational(lower, row, upper).
        spx.addRowRational(LPRowRational(lhs, row, rhs));
    }

    void addEQ(const Lin &terms, const Rat &rhs) { addRow(terms, rhs, rhs); }

    void addLE(const Lin &terms, const Rat &rhs) { addRow(terms, -infinity, rhs); }

    void addGE(const Lin &terms, const Rat &rhs) { addRow(terms, rhs, infinity); }
};

int to_ind(int i, int j) { return i * M + j; }

vector<Lin> group_to_options(vector<vector<int>> const &group) {
    vector<Lin> result;
    for (int i = 0; i < N; ++i) {
        // Total value of agent i's own bundle.
        Lin total;
        for (int j : group[i]) {
            total.push_back({to_ind(i, j), +1});
        }

        for (int j = 0; j < N; ++j) {
            if (i == j) {
                continue;
            }

            if (group[j].size() <= 1) {
                continue;
            }

            // Total value of agent j's bundle according to i's valuations.
            for (int k : group[j]) {
                auto diff = total;
                for (int d : group[j]) {
                    if (d == k) {
                        continue;
                    }
                    diff.push_back({to_ind(i, d), -1});
                }
                diff.push_back({N * M, +1}); // eps
                // our - (diff w/o 1(k)) + eps <= 0
                // our < diff w/o 1(k)
                result.push_back(diff);
            }
        }
    }
    return result;
}

vector<vector<Lin>> groups_to_ineqs(vector<vector<vector<int>>> const &groups) {
    size_t n = groups.size();
    vector<vector<Lin>> result(n);
    for (size_t i = 0; i < n; i++) {
        result[i] = group_to_options(groups[i]);
    }
    return result;
}

Lin add(Lin x, Lin const &y) {
    for (auto [var, coef] : y) {
        bool found = false;
        for (auto &[vv, cc] : x) {
            if (var == vv) {
                cc += coef;
                found = true;
            }
        }

        if (!found) {
            x.push_back({var, coef});
        }
    }
    return x;
}

Lin neg(Lin x) {
    for (auto &[var, coef] : x) {
        coef *= -1;
    }
    return x;
}

struct State {
    vector<int> path;

    friend bool operator<(State const &f, State const &s) { return f.path.size() < s.path.size(); }
};

bool solve_node(State const &s, vector<vector<Lin>> const &options) {
    ExactLP m;

    array<int, N * M + 1> vars;
    for (size_t i = 0; i < N * M; i++) {
        vars[i] = m.addVar();
    }

    // Strictness slack, maximized.
    vars.back() = m.addVar(1, 1, infinity); // eps

    for (size_t i = 0; i + 1 < M; i++) {
        m.addLE({{vars[i], 1}, {vars[i + 1], -1}}, 0); // vars[i] <= vars[i + 1]
    }

    for (size_t i = 0; i < s.path.size(); i++) {
        auto ineq = options[i][s.path[i]];
        for (auto &[ind, coef] : ineq) {
            ind = vars[ind];
        }

        m.addLE(ineq, 0);
    }

    auto stat = m.spx.optimize();
    if (stat == SPxSolver::INFEASIBLE) {
        return false;
    }

    assert(stat == SPxSolver::UNBOUNDED);
    return true;
}

static void print_path(std::ostream &os, State const &state) {
    os << "PATH=[";
    for (size_t i = 0; i < state.path.size(); ++i) {
        if (i) {
            os << ", ";
        }
        os << state.path[i];
    }
    os << "]\n";
}

template <class T> struct TaskQueue {
    atomic<int> working;
    queue<T> q;
    mutex mtx;

    TaskQueue(int n) : working(n) {}

    optional<T> pop() {
        --working;
        do {
            {
                lock_guard lock(mtx);
                if (!q.empty()) {
                    auto res = q.front();
                    q.pop();
                    ++working;
                    return res;
                }
            }

            std::osyncstream{std::cerr} << "Sleeping " << std::this_thread::get_id() << " - " << working << endl;
            this_thread::sleep_for(1s);
        } while (working);
        ++working;
        return nullopt;
    }

    void push(T t) {
        lock_guard lock(mtx);
        q.push(t);
    }

    void stop() { --working; }

    bool empty() const { return q.empty(); }
};

void worker(TaskQueue<State> &q, vector<vector<Lin>> const &options, atomic<long long> &total, mutex &print_mutex) {
    while (auto task = q.pop()) {
        auto x = ++total;

        bool should_print = x % (int)1e4 == 0;
        if (should_print) {
            lock_guard lock{print_mutex};
            // std::osyncstream ss{std::cerr};
            auto &ss = std::cerr;
            ss << "Task #" << x << " -> " << task->path.size() << endl;
            print_path(ss, *task);
            ss.flush();
        }

        auto solvable = solve_node(*task, options);
        if (!solvable) {
            continue;
        }

        size_t sz = task->path.size();
        bool found = sz == options.size();
        if (found) {
            lock_guard lock{print_mutex};
            // std::osyncstream ss{std::cout};
            auto &ss = std::cerr;

            ss << "FOUND!!!" << endl;
            print_path(ss, *task);
            ss.flush();
            exit(0);
        }

        for (int next_ineq = 0; next_ineq < options[sz].size(); ++next_ineq) {
            auto next_task = task.value();
            next_task.path.push_back(next_ineq);
            q.push(next_task);
        }
    }

    q.stop();
}

int main() {
    cout << "N=" << N << " M=" << M << std::endl;

    unsigned threads = std::max(1u, std::thread::hardware_concurrency());
    cout << "Using " << threads << " threads\n";

    auto groups = ordered_groups(N, M);
    std::cout << "Number of partitions = " << groups.size() << std::endl;

    sort(begin(groups), end(groups), [](auto const &f, auto const &s) { return f.size() < s.size(); });

    auto ineqs = groups_to_ineqs(groups);

    TaskQueue<State> q(threads);
    q.push({});

    std::vector<std::thread> pool;
    pool.reserve(threads);

    atomic<long long> tasks_done{0};
    mutex print_mutex;
    for (unsigned t = 0; t < threads; ++t) {
        pool.emplace_back([&] { worker(std::ref(q), std::ref(ineqs), std::ref(tasks_done), std::ref(print_mutex)); });
    }

    for (auto &th : pool) {
        th.join();
    }

    assert(q.empty());
    cout << "Done\n";
    cout << "Total nodes: " << tasks_done << "\n";
    return 0;
}
