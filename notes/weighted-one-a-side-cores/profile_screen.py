"""Apply the two quotient profiles to physical 5-by-5 tables."""
from collections import Counter
from itertools import permutations

FAMILIES = {'overlapping': (0, 3, 5), 'disjoint': (1, 2, 5)}


def quotient(mask):
    rows = tuple(tuple(mask >> (5 * r + c) & 1 for c in range(5)) for r in range(5))
    cols = tuple(zip(*rows))
    counts_r, counts_c = Counter(rows), Counter(cols)
    if (len(counts_r), len(counts_c)) != (3, 3):
        return None
    for rs in permutations(counts_r):
        for cs in permutations(counts_c):
            ci = [cols.index(c) for c in cs]
            form = tuple(sum(line[i] << c for c, i in enumerate(ci)) for line in rs)
            for family, expected in FAMILIES.items():
                if form == expected:
                    return family, tuple(counts_r[r] for r in rs), tuple(counts_c[c] for c in cs)
    return None


def min_cost(profile, rows, cols):
    return min(cost + sum(size - 1 for i,size in enumerate(rows) if i != rd)
                    + sum(size - 1 for i,size in enumerate(cols) if i != cd)
               for (rd,cd),cost in profile.items())


def closed_forms(family, a, b):
    total = sum(a) + sum(b)
    if family == 'overlapping':
        row_saving = max(0, a[0] - 1, a[1] - 2, a[2] - 2)
        col_saving = max(b) - 1
        return total - a[0], total - 1 - row_saving - col_saving
    row_saving = max(0, a[0] - 1, a[1] - 2, a[2] - 1)
    col_saving = max(0, b[0] - 1, b[1] - 2, b[2] - 1)
    return total, total - row_saving - col_saving
