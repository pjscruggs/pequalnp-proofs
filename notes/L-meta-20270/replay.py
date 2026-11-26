"""Exact gate count for an OR of at most four products of input unions."""
from collections import Counter
from functools import lru_cache
from itertools import combinations
from math import inf


MASK = 7093347072485314830
N = 8


def elements(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def subsets(mask):
    sub = mask
    while sub:
        yield sub
        sub = (sub - 1) & mask


def rectangles(mask):
    result = []
    for left in range(1, 1 << N):
        common = (1 << N) - 1
        for i in elements(left):
            common &= mask >> (N * i)
        for right in subsets(common):
            cells = sum(right << (N * i) for i in elements(left))
            result.append((left, right, cells))
    return result


def products(mask):
    rects = rectangles(mask)
    terms = [(left, right << N, cells) for left, right, cells in rects]
    for (a, b, edges), (c, d, other) in combinations(rects, 2):
        if not (a & c or b & d):
            terms.append((a | (d << N), c | (b << N), edges | other))
    return terms


def covers(mask, terms, cap):
    containing = {bit: [] for bit in elements(mask)}
    for i, (_, _, cells) in enumerate(terms):
        for bit in elements(cells):
            containing[bit].append(i)
    max_cells = max(cells.bit_count() for _, _, cells in terms)
    result = set()

    def visit(remaining, prefix):
        if not remaining:
            result.add(tuple(sorted(prefix)))
            return
        slots = cap - len(prefix)
        if remaining.bit_count() > slots * max_cells:
            return
        bit = min(elements(remaining), key=lambda bit: len(containing[bit]))
        for i in containing[bit]:
            rest = remaining & ~terms[i][2]
            if rest.bit_count() <= (slots - 1) * max_cells:
                visit(rest, prefix + (i,))

    visit(mask, ())
    return sorted(result)


def union_cost(outputs):
    targets = set(outputs)
    multiplicity = Counter(s for t in targets for s in subsets(t) if s.bit_count() >= 2)
    optional = [s for s, n in multiplicity.items() if n > 1 and s not in targets]
    mandatory = {s for s in targets if s.bit_count() > 1}

    @lru_cache(None)
    def local(target, available):
        candidates = [1 << i for i in elements(target)] + list(available)

        @lru_cache(None)
        def min_terms(remaining):
            if not remaining:
                return 0
            pivot = remaining & -remaining
            return 1 + min(min_terms(remaining & ~x) for x in candidates if x & pivot)

        return min_terms(target) - 1

    best = inf
    for selector in range(1 << len(optional)):
        signals = mandatory | {optional[i] for i in elements(selector)}
        total = 0
        for s in signals:
            available = tuple(sorted(t for t in signals if t != s and t & s == t))
            total += local(s, available)
        best = min(best, total)
    return best


def main():
    terms = products(MASK)
    raw_inputs = [(1 << r) | (1 << (N + c)) for r in range(N) for c in range(N)]
    for a, b, cells in terms:
        actual = sum(1 << i for i, x in enumerate(raw_inputs) if x & a and x & b)
        assert actual == cells and cells & ~MASK == 0
    solutions = covers(MASK, terms, 4)
    assert len(rectangles(MASK)) == 93 and len(terms) == 2812
    assert Counter(map(len, solutions)) == {4: 128}
    print("nonempty rectangles", len(rectangles(MASK)), "normalized products", len(terms))
    print("covers by number of products", dict(sorted(Counter(map(len, solutions)).items())))
    costs = Counter()
    for choice in solutions:
        inputs = [s for i in choice for s in terms[i][:2]]
        # A one-rectangle term could have extra irrelevant indicators in its input unions.
        # Every cover here needs two nonempty rectangles in each term.
        assert all(s & 255 and s >> 8 for s in inputs)
        costs[union_cost(inputs) + 2 * len(choice) - 1] += 1
    print("covers by minimum gate count", dict(sorted(costs.items())))
    assert costs == {25: 18, 26: 34, 27: 32, 28: 28, 29: 14, 30: 2}


if __name__ == "__main__":
    main()
