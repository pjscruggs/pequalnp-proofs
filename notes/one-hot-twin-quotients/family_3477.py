"""Classify desk mask bounds with the same pendant-leaf core as L-meta-23705."""

import argparse
import itertools
import json
import re
import sys
from pathlib import Path

from twin_core import essential_inputs, input_tables


def transpose(rows):
    return tuple(zip(*rows))


def core_shape(rows):
    rows = tuple(dict.fromkeys(row for row in rows if not all(row)))
    cols = tuple(dict.fromkeys(col for col in transpose(rows) if not all(col)))
    rows = transpose(cols)
    if len(rows) == 5 and len(cols) == 3:
        rows = cols
    if len(rows) != 3 or len(rows[0]) != 5:
        return None
    return min(tuple(sorted(zip(*perm))) for perm in itertools.permutations(rows))


def matrix(rows, columns, mask):
    return tuple(
        tuple(mask >> (columns * row + col) & 1 for col in range(columns))
        for row in range(rows)
    )


def classify(path):
    target = core_shape(matrix(3, 5, 3477))
    assert target is not None
    pattern = re.compile(
        r"^PEqualNP\.Represents\.RepSizeAtMost \(fun \(u : Fin (\d+)\) \(v : Fin (\d+)\)"
        r" => \((\d+) : ℕ\)\.testBit \((\d+) \* u.val \+ v.val\)\) (\d+)$"
    )
    data = json.loads(Path(path).read_text(encoding="utf-8-sig"))
    print("gap\trows\tcolumns\tmask\tposted_cap\texact_cost\tofferable\topen_prs")
    count = below = offerable = 0
    for gap in data["gaps"]:
        statement = pattern.match(gap.get("statement", ""))
        if not statement:
            continue
        rows, columns, mask, stride, cap = map(int, statement.groups())
        if stride != columns or min(rows, columns) < 3:
            continue
        if core_shape(matrix(rows, columns, mask)) == target:
            cost = rows + columns + 1
            is_offerable = gap.get("offerable_now")
            assert essential_inputs(mask, input_tables(rows, columns), rows * columns) == set(
                range(rows + columns)
            )
            print(gap["id"], rows, columns, mask, cap, cost, is_offerable, gap.get("pr_open"),
                  sep="\t")
            count += 1
            below += cap < cost
            offerable += cap < cost and is_offerable is True
    print(f"{count} matches, {below} bounds below the exact cost, {offerable} offerable at capture.",
          file=sys.stderr)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("catalog", type=Path, help="JSON snapshot of the desk gaps.")
    classify(parser.parse_args().catalog)
