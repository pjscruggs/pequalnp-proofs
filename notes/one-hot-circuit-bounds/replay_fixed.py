"""Replay the fixed-family lower bounds on a local copy of L_meta_19358.lean."""
import re
import sys
from collections import Counter
from fractions import Fraction
from math import ceil, lcm
from pathlib import Path


def supports(path):
    source = path.read_text(encoding="utf-8-sig")
    codes = re.findall(r"\((true|false),(\d+),(\d+)\)", source.split("def codes", 1)[1].split("def circuit", 1)[0])
    wires = [1 << i for i in range(256)]
    products = []
    for op, left, right in codes:
        a, b = wires[int(left)], wires[int(right)]
        if op == "true":
            wires.append(None if a is None or b is None else a | b)
        else:
            assert a is not None and b is not None
            products.append((a, b))
            wires.append(None)
    assert len(codes) == 1500 and len(products) == 64
    return [s for pair in products for s in pair]


def local_counts(target, others):
    points = [1 << i for i in range(target.bit_length()) if target >> i & 1]
    counts = Counter()
    for other in others:
        intersection = sum(1 << j for j, p in enumerate(points) if other & p)
        sub = intersection
        while sub:
            if sub & (sub - 1):
                counts[sub] += 1
            sub = (sub - 1) & intersection
    return len(points), counts


def bound(family, private):
    prices = []
    for i, target in enumerate(family):
        n, counts = local_counts(target, family[:i] + family[i+1:])
        scale = 1 if private else lcm(*(v + 1 for v in counts.values()))
        # Each local mask with nonzero saving belongs to at least two outputs.
        candidates = [[] for _ in range(n)]
        saving = [0] * (1 << n)
        for mask, others in counts.items():
            saving[mask] = scale if private else scale - scale // (1 + others)
            candidates[(mask & -mask).bit_length() - 1].append(mask)
        for mask in range(1, 1 << n):
            first = mask & -mask
            best = saving[mask ^ first]
            for component in candidates[first.bit_length() - 1]:
                if component < mask and component & mask == component:
                    best = max(best, saving[component] + saving[mask ^ component])
            saving[mask] += best
        prices.append(Fraction((n-1)*scale - saving[-1], scale))
    return prices


def main(path):
    outputs = supports(path)
    row_mask = (1 << 128) - 1
    row = [s & row_mask for s in outputs]
    col = [s >> 128 for s in outputs]
    assert len(set(row)) == len(set(col)) == 128
    fixed = bound(outputs, False)
    row_private = bound(row, True)
    col_private = bound(col, True)
    print("fixed OR charge", sum(fixed), "fixed topology", ceil(sum(fixed))+127)
    loss = [v - (a+b)/2 for v, a, b in zip(fixed, row_private, col_private)]
    pair_loss = sorted((a+b for a, b in zip(loss[::2], loss[1::2])), reverse=True)
    for s in [0, 17, 24, 25, 26]:
        charge = sum(fixed) - sum(pair_loss[:s])
        print(s, "changed products:", charge, "OR charge, total >=", ceil(charge)+127)


if __name__ == "__main__":
    main(Path(sys.argv[1]))
