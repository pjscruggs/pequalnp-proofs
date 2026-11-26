"""Exhaust one-a-side circuit budgets on the four-by-three path-plus-edge core."""
from functools import cache
from itertools import combinations, product

CELLS = tuple(product(range(4), range(3)))
FULL = (1 << len(CELLS)) - 1


def reachable(target, row_default, col_default, signed, budget):
    inputs = tuple(
        sum(1 << index for index, pair in enumerate(CELLS) if pair[shore] == value)
        for shore, default in enumerate((row_default, col_default))
        for value in range((4, 3)[shore]) if value != default
    )
    pairs = tuple((i, j) for i, j in product(range(len(CELLS)), repeat=2)
                  if target >> i & 1 and not target >> j & 1)

    @cache
    def separation(signal):
        return sum(1 << k for k, (i, j) in enumerate(pairs)
                   if ((signal >> i ^ signal >> j) & 1 if signed
                       else (signal >> i & 1) and not (signal >> j & 1)))

    needed = (1 << len(pairs)) - 1

    @cache
    def search(live, left):
        if target in live:
            return True
        if not left or len(live) > left + 1:
            return False
        seen = 0
        for signal in live:
            seen |= separation(signal)
        if seen != needed:
            return False

        def extend(parents, signal):
            if signal in live or signal in (0, FULL):
                return False
            other = tuple(v for v in live if v not in parents)
            for k in range(len(parents) + 1):
                if len(other) + 1 + k > left:
                    break
                for kept in combinations(parents, k):
                    new = tuple(sorted(other + kept + (signal,)))
                    if search(new, left - 1):
                        return True
            return False

        if signed and any(extend((x,), FULL ^ x) for x in live):
            return True
        for x, y in combinations(live, 2):
            if extend((x, y), x & y) or extend((x, y), x | y):
                return True
        return False

    return any(search(tuple(sorted(chosen)), budget)
               for count in range(1, min(budget + 1, len(inputs)) + 1)
               for chosen in combinations(inputs, count))
