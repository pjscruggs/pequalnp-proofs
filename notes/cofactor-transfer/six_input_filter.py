"""Classify six-input monotone truth tables by deletion, AND/OR substitution and duality.

Python 3.10+. With a numeric argument, print a reduction for that truth table
(hexadecimal is accepted with a 0x prefix). Without one, enumerate the census.
Bit a of a table is the value at assignment a, with input i at bit i of a.
"""
import sys
from collections import Counter
from itertools import combinations

N = 6
FULL = (1 << (1 << N)) - 1
X = [sum(1 << a for a in range(64) if a >> i & 1) for i in range(N)]


def reductions(f):
    for i in range(N):
        shift = 1 << i
        low = f & ~X[i]
        high = (f & X[i]) >> shift
        if low == high:
            yield ('unused', i, 0)
        elif low == 0 and high != FULL ^ X[i]:
            yield ('output AND', i, 1)
        elif high == FULL ^ X[i] and low != 0:
            yield ('output OR', i, 0)
    for i, j in combinations(range(N), 2):
        mask = FULL ^ (X[i] | X[j])
        a, b = 1 << i, 1 << j
        p, q, r, s = [(f >> k) & mask for k in (0, a, b, a+b)]
        if p == q == r and p != s:
            yield ('input AND', i, j, 1)
        if q == r == s and p != s:
            yield ('input OR', i, j, 0)


def neighbors(f):
    for i in range(N - 1):
        delta = 1 << i
        mask = X[i] & ~X[i+1]
        diff = (f ^ (f >> delta)) & mask
        yield f ^ diff ^ (diff << delta)


def dual(f):
    return FULL ^ int(f'{f:064b}'[::-1], 2)


def orbit(f):
    seen, todo = {f}, [f]
    while todo:
        for g in neighbors(todo.pop()):
            if g not in seen:
                seen.add(g)
                todo.append(g)
    return seen


def main():
    if len(sys.argv) == 2:
        f = int(sys.argv[1], 0)
        for rule in reductions(f):
            i, value = rule[1], rule[-1]
            inputs = [a for a in range(64) if (a >> i & 1) == value]
            parent = sum(((f >> a) & 1) << j for j, a in enumerate(inputs))
            print(rule, f'parent=0x{parent:08x}')
        return
    tables = [0, 1]
    for n in range(1, 6):
        tables = [a | (b << (1 << (n-1))) for a in tables for b in tables if a & ~b == 0]
    assert len(tables) == 7581
    pending = {a | (b << 32) for a in tables for b in tables if a & ~b == 0}
    assert len(pending) == 7828354
    counts = Counter()
    while pending:
        f = pending.pop()
        group = orbit(f)
        other = dual(f)
        self_dual = other in group
        combined = group if self_dual else group | orbit(other)
        pending.difference_update(combined)
        kind = 'reducible' if next(reductions(f), None) else 'residual'
        counts[kind, 'labeled'] += len(combined)
        counts[kind, 'permutation'] += 1 if self_dual else 2
        counts[kind, 'permutation and duality'] += 1
    assert sum(counts[k, 'permutation'] for k in ('reducible', 'residual')) == 16353
    for key, value in sorted(counts.items()):
        print(*key, value, sep=' | ')


if __name__ == '__main__':
    main()
