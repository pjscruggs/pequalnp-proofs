"""Check the five-point quotient and eight-gate witness for L-meta-24351."""

from functools import cache, reduce
from itertools import combinations, combinations_with_replacement
from operator import or_

CORE_MASK = 266717
PAIRS = tuple(combinations_with_replacement(range(5), 2))
TABLE_MASK = (1 << len(PAIRS)) - 1
TARGET = sum(
    ((CORE_MASK >> (5 * i + j)) & 1) << pos
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


SIX_POINT_MASK = 270649273
CORE_POINTS = (0, 1, 3, 4, 5)
WITNESS = (
    ("not", 0), ("or", 1, 2), ("and", 3, 4), ("and", 5, 6),
    ("and", 0, 7), ("or", 8, 9), ("or", 10, 11), ("not", 12),
)


def entry(mask, n, i, j):
    return bool((mask >> (n * min(i, j) + max(i, j))) & 1)


def check_witness():
    for i in range(6):
        for j in range(6):
            wires = [k in (i, j) for k in range(6)]
            for op, a, *rest in WITNESS:
                assert 0 <= a < len(wires)
                if op == "not":
                    assert not rest
                    wires.append(not wires[a])
                else:
                    (b,) = rest
                    assert 0 <= b < len(wires)
                    assert op in ("and", "or")
                    wires.append(wires[a] and wires[b] if op == "and" else wires[a] or wires[b])
            assert wires[-1] == entry(SIX_POINT_MASK, 6, i, j), (i, j)


if __name__ == "__main__":
    assert all(entry(SIX_POINT_MASK, 6, i, 1) == entry(SIX_POINT_MASK, 6, i, 2) for i in range(6))
    assert entry(SIX_POINT_MASK, 6, 0, 0) != entry(SIX_POINT_MASK, 6, 0, 2)
    for i, j in PAIRS:
        assert entry(CORE_MASK, 5, i, j) == entry(SIX_POINT_MASK, 6, CORE_POINTS[i], CORE_POINTS[j])
    # A differing singleton and pair witness that each core input is necessary.
    for i in range(5):
        assert any(j != i and entry(CORE_MASK, 5, j, j) != entry(CORE_MASK, 5, i, j) for j in range(5))
    assert not feasible(tuple(sorted(INPUTS)), 6)
    assert len(WITNESS) == 8
    check_witness()
    print("Core cannot be computed with six gates.", feasible.cache_info())
    print("Eight-gate witness verified for all 36 promised inputs.")
