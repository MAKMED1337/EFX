from typing import Generator, cast
from z3 import And, ArithRef, Not, Or, Real, Solver, Sum, BoolRef, unsat
import itertools

N, M = 4, 6


# Method to generate all splits (written by deepseek)
def ordered_groups(elements: list[int], num_groups: int) -> Generator[list[list[int]]]:
    """
    Generate all ways to split `elements` into `num_groups` non‑empty *ordered* groups.
    Yields a tuple of `num_groups` tuples, where the i‑th tuple contains the elements
    assigned to group i (groups are labeled 0..num_groups-1).
    """
    n = len(elements)
    groups = range(num_groups)

    # All assignments of elements to group labels
    for assignment in itertools.product(groups, repeat=n):
        # Keep only assignments where every group gets at least one element
        if len(set(assignment)) != num_groups:
            continue

        # Build the groups: list of lists, one per group
        group_lists: list[list[int]] = [[] for _ in groups]
        for elem, g in zip(elements, assignment):
            group_lists[g].append(elem)

        # Sort each group's elements for consistent output
        for lst in group_lists:
            lst.sort()

        # Convert to immutable tuple of tuples
        yield list(list(lst) for lst in group_lists)


def weight(i: int, j: int) -> ArithRef:
    return Real(f"w_{i}_{j}")


def nonenvy(partition: list[list[int]]) -> BoolRef:
    ineqs: list[BoolRef] = []
    for i in range(N):
        # Our weight
        total = cast(ArithRef, Sum(weight(i, el) for el in partition[i]))
        for j in range(N):
            if i == j:
                continue

            # Other weight
            other = cast(ArithRef, Sum(weight(i, el) for el in partition[j]))

            # We are happy if we have more if we remove any element from another person
            for k in partition[j]:
                ineqs.append(total >= other - weight(i, k))

    # Take and across all "opponents" and their items
    return cast(BoolRef, And(*ineqs))


def main() -> None:
    elements = list(range(M))
    partitions = list(ordered_groups(elements, N))
    # print(partitions)
    print('number of partitions =', len(partitions))

    solver = Solver()
    # Set all weights to be positive
    for i in range(N):
        for j in range(M):
            solver.add(weight(i, j) > 0)

    # Boolean indicator if this partition can be valid (depends on weights)
    is_valid = [nonenvy(partition) for partition in partitions]

    # To find a counterexample there should be weights for it is false for every partition
    solver.add(Not(Or(*is_valid)))

    print(solver)

    if solver.check() == unsat:
        print("No counterexample :(")
    else:
        print("Exmaple:")
        print(solver.model())


if __name__ == "__main__":
    main()
