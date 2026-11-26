"""Compute exact one-a-side costs for a three-by-three Boolean table."""
from functools import cache
from itertools import combinations, product

CELLS = tuple(product(range(3), repeat=2))
FULL = (1 << len(CELLS)) - 1


def optimum(target, row_default, col_default, signed):
    inputs = tuple(
        sum(1 << index for index, pair in enumerate(CELLS) if pair[shore] == value)
        for shore, default in enumerate((row_default, col_default))
        for value in range(3) if value != default
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

    for budget in range(9):
        if any(search(tuple(sorted(chosen)), budget)
               for count in range(1, min(budget + 1, len(inputs)) + 1)
               for chosen in combinations(inputs, count)):
            return budget
    raise RuntimeError('No witness within the search budget')


def profile(target, signed):
    rows = [sum(((target >> (3 * r + c)) & 1) << c for c in range(3)) for r in range(3)]
    cols = [sum(((target >> (3 * r + c)) & 1) << r for r in range(3)) for c in range(3)]
    def possible(neighborhoods):
        return (None, *(i for i, mask in enumerate(neighborhoods)
                         if signed or all(mask & other == mask for other in neighborhoods)))
    return {(r, c): optimum(target, r, c, signed)
            for r, c in product(possible(rows), possible(cols))}


if __name__ == '__main__':
    for name, rows in [('overlapping', (0, 3, 5)), ('disjoint', (1, 2, 5))]:
        target = sum(mask << (3 * r) for r, mask in enumerate(rows))
        for signed in (False, True):
            print(name, 'signed' if signed else 'monotone', profile(target, signed))
