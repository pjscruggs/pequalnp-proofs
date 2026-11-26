"""Replay exact synthesis for desk L-meta-23799 on five-point two-lit inputs."""

from functools import cache, reduce
from itertools import combinations, combinations_with_replacement
from operator import or_

PAIRS = tuple(combinations_with_replacement(range(5), 2))
TABLE_MASK = (1 << len(PAIRS)) - 1
TARGET = sum(
    ((283359 >> (5 * i + j)) & 1) << pos
    for pos, (i, j) in enumerate(PAIRS)
)
INPUTS = tuple(
    sum(1 << pos for pos, pair in enumerate(PAIRS) if point in pair)
    for point in range(5)
)
ROWS_TO_SEPARATE = tuple(
    (a, b)
    for a, b in combinations(range(len(PAIRS)), 2)
    if (TARGET >> a ^ TARGET >> b) & 1
)


@cache
def distinctions(table):
    return sum(
        1 << pos
        for pos, (a, b) in enumerate(ROWS_TO_SEPARATE)
        if (table >> a ^ table >> b) & 1
    )


@cache
def feasible(frontier, remaining):
    if TARGET in frontier:
        return True
    if not remaining or len(frontier) > remaining + 1:
        return False
    if reduce(or_, map(distinctions, frontier), 0) != distinctions(TARGET):
        return False

    def extend(consumed, value):
        if value in frontier or value in (0, TABLE_MASK):
            return False
        rest = tuple(table for table in frontier if table not in consumed)
        for uses in range(len(consumed) + 1):
            for kept in combinations(consumed, uses):
                new_frontier = tuple(sorted(rest + kept + (value,)))
                if feasible(new_frontier, remaining - 1):
                    return True
        return False

    for a in frontier:
        if extend((a,), TABLE_MASK ^ a):
            return True
    for a, b in combinations(frontier, 2):
        if extend((a, b), a & b) or extend((a, b), a | b):
            return True
    return False


def verify_witness():
    values = list(INPUTS)
    values.append(values[1] | values[2])
    values.append(values[0] | values[5])
    values.append(TABLE_MASK ^ values[6])
    values.append(values[4] & values[7])
    values.append(values[3] & values[5])
    values.append(values[8] | values[9])
    values.append(TABLE_MASK ^ values[10])
    return values[-1] == TARGET


if __name__ == "__main__":
    # Each designated singleton differs from its pair by one variable.
    for i, j in enumerate((4, 3, 3, 1, 3)):
        singleton = PAIRS.index((j, j))
        pair = PAIRS.index(tuple(sorted((i, j))))
        assert (TARGET >> singleton ^ TARGET >> pair) & 1
    assert not feasible(tuple(sorted(INPUTS)), 6)
    assert verify_witness()
    print("Exact optimum 7. Six-gate search cache:", feasible.cache_info())
