import itertools


def is_efx_chores(costs, allocation):
    # Same EFX check function as before
    assigned = [False] * 6
    for bundle in allocation:
        for g in bundle:
            if not (0 <= g < 6):
                return False, f"Invalid good index {g}"
            if assigned[g]:
                return False, f"Good {g} assigned multiple times"
            assigned[g] = True
    if not all(assigned):
        missing = [i for i, a in enumerate(assigned) if not a]
        return False, f"Goods {missing} not assigned"

    total_cost = [sum(costs[i][g] for g in allocation[i]) for i in range(4)]

    for i in range(4):
        for j in range(4):
            if i == j:
                continue
            for g in allocation[j]:
                reduced_cost = sum(costs[i][g2] for g2 in allocation[j] if g2 != g)
                if total_cost[i] < reduced_cost:
                    return False, f"Agent {i} envies agent {j} after removing good {g}"
    return True, "EFX"


costs = [
    [2, 2, 2, 2, 2, 3],
    [1, 2, 4, 7, 12, 20],
    [1, 2, 4, 7, 12, 20],
    [1, 2, 4, 7, 12, 20],
]

efx_allocations = []

# Enumerate assignments for goods 0..4 (5 goods) among 4 agents
total = 0
for assignment in itertools.product(range(4), repeat=5):
    total += 1

    allocation = [[] for _ in range(4)]
    # Goods 0..4
    for g, agent in enumerate(assignment):
        allocation[agent].append(g)
    # Good 5 always to agent 0
    allocation[0].append(5)

    ok, _ = is_efx_chores(costs, allocation)
    if ok:
        efx_allocations.append(allocation)

print(f"Assignments checked (good 5 fixed to agent 0): {4**5} = {total}")
print(f"Number of EFX allocations: {len(efx_allocations)}")

if efx_allocations:
    print("\nFirst 5 EFX allocations (bundles for agents 0,1,2,3):")
    for alloc in efx_allocations[:5]:
        print(alloc)
else:
    print("No EFX allocation exists with good 5 assigned to agent 0.")
