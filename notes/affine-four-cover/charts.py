"""Emit verified overlap constraints on the point masks used by L-meta-9348."""
import argparse
from itertools import permutations
import json

from affine_extension_cnf import AFFINE, LINE_LABEL, POINT_LABEL, SHAPES, SWARM_ROWS


def move(mask, permutation):
    return sum(1 << image for i, image in enumerate(permutation) if mask >> i & 1)


def affine_families():
    lines = {sum(1 << i for i, row in enumerate(AFFINE) if row >> j & 1) for j in range(20)}
    origin_lines = {line for line in lines if line & 1}
    translations = [tuple(i ^ t for i in range(16)) for t in range(16)]
    assert all({move(line, tr) for line in lines} == lines for tr in translations)
    families = set()
    count = 0
    for basis in permutations(range(1, 16), 4):
        perm = [0]
        for vector in basis:
            perm += [p ^ vector for p in perm]
        if len(set(perm)) != 16 or {move(line, perm) for line in origin_lines} != origin_lines:
            continue
        assert {move(line, perm) for line in lines} == lines
        count += 1
        for tr in translations:
            point_map = [POINT_LABEL[tr[i]] for i in perm]
            families.add(tuple(sorted(move(shape, point_map) for shape in SHAPES)))
    assert count == 360
    return families


def charts():
    families = affine_families()
    domain = sum(1 << p for p in POINT_LABEL[:16])
    for shift in range(21):
        rotation = [(p + shift) % 21 for p in range(21)]
        assert all(move(row, rotation) == SWARM_ROWS[rotation[i]] for i, row in enumerate(SWARM_ROWS))
        infinity_line = rotation[LINE_LABEL[20]]
        affine_points = move(domain, rotation)
        assert affine_points == sum(1 << p for p, row in enumerate(SWARM_ROWS) if not row >> infinity_line & 1)
        for family in sorted(families):
            yield dict(infinity_line=infinity_line, affine_points=affine_points,
                       traces=sorted(move(s, rotation) for s in family), max_matches=7)


def dual_chart(chart):
    # Under this polarity, point i is sent to line -i and line j to point -j.
    polarity = [(-i) % 21 for i in range(21)]
    assert all((row >> j & 1) == (SWARM_ROWS[polarity[j]] >> polarity[i] & 1)
               for i, row in enumerate(SWARM_ROWS) for j in range(21))
    return dict(infinity_point=polarity[chart["infinity_line"]],
                affine_lines=move(chart["affine_points"], polarity),
                traces=sorted(move(s, polarity) for s in chart["traces"]), max_matches=7)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--emit", action="store_true", help="emit one JSON constraint per line")
    parser.add_argument("--dual", action="store_true", help="emit constraints on rectangle columns")
    args = parser.parse_args()
    constraints = list(charts())
    assert len({(c["affine_points"], tuple(c["traces"])) for c in constraints}) == len(constraints)
    if args.dual:
        constraints = [dual_chart(c) for c in constraints]
    if args.emit:
        for item in constraints:
            print(json.dumps(item))
    else:
        side = "column" if args.dual else "row"
        print(f"{len(constraints)} distinct {side} constraints.")
