#include <algorithm>
#include <functional>
#include <vector>

// Generate all ordered partitions of {0,...,M-1} into N non-empty groups.
// Groups are ordered (labeled 0..N-1).
std::vector<std::vector<std::vector<int>>> ordered_groups(const int N, const int M) {
    std::vector<std::vector<std::vector<int>>> result;
    std::vector<int> assignment(M); // assignment[i] = group label of item i
    std::function<void(int)> generate = [&](int idx) {
        if (idx == M) {
            // Check that every group is non-empty.
            std::vector<int> count(N);
            for (int i = 0; i < M; ++i) {
                count[assignment[i]]++;
            }
            for (int g = 0; g < N; ++g) {
                if (count[g] == 0) {
                    return;
                }
            }

            // Build the groups.
            std::vector<std::vector<int>> groups(N);
            for (int i = 0; i < M; ++i) {
                groups[assignment[i]].push_back(i);
            }
            // Sort each group for consistency (not required for logic).
            for (auto &g : groups) {
                std::sort(g.begin(), g.end());
            }
            result.push_back(std::move(groups));
            return;
        }
        for (int g = 0; g < N; ++g) {
            assignment[idx] = g;
            generate(idx + 1);
        }
    };
    generate(0);
    return result;
}
