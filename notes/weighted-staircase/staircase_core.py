"""Compute the exact gate profile of the three-by-three staircase core."""
from functools import cache
from itertools import combinations, product

CELLS = tuple(product(range(3), repeat=2))
FULL = (1 << len(CELLS)) - 1
TARGET = sum(1 << i for i, (r, c) in enumerate(CELLS) if r and c and r + c >= 3)


def optimum(row_default, col_default, signed):
    inputs = tuple(
        sum(1 << index for index, pair in enumerate(CELLS) if pair[shore] == value)
        for shore, default in enumerate((row_default, col_default))
        for value in range(3) if value != default
    )
    pairs = tuple((i, j) for i, j in product(range(len(CELLS)), repeat=2)
                  if TARGET >> i & 1 and not TARGET >> j & 1)

    @cache
    def separation(signal):
        return sum(1 << k for k, (i, j) in enumerate(pairs)
                   if ((signal >> i ^ signal >> j) & 1 if signed
                       else (signal >> i & 1) and not (signal >> j & 1)))

    needed = (1 << len(pairs)) - 1

    @cache
    def search(live, left):
        if TARGET in live:
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


def profile(signed):
    # Empty row and column are both type zero. In the monotone basis only they can be hidden.
    defaults = (None, 0, 1, 2) if signed else (None, 0)
    return {(r, c): optimum(r, c, signed) for r, c in product(defaults, repeat=2)}


if __name__ == '__main__':
    for signed in (False, True):
        print('signed' if signed else 'monotone', profile(signed))
