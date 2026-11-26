"""Screen a saved public desk catalog for obstructions to the essential-input floor."""

import argparse
import json
import re
from itertools import combinations, product
from pathlib import Path

MASK_STATEMENT = re.compile(
    r"\((\d+) : ℕ\)\.testBit \((\d+) \* u.val \+ v.val\)\) (\d+)$"
)


def can_split(neighborhoods):
    for i, neighbors in enumerate(neighborhoods):
        rest = set(neighborhoods[:i] + neighborhoods[i + 1:])
        if any(a & b for a, b in combinations(rest, 2)):
            continue
        for labels in product((False, True), repeat=len(neighbors)):
            left = frozenset(c for c, label in zip(neighbors, labels) if label)
            right = neighbors - left
            if left and right and all(s == t or not s & t for s in rest for t in (left, right)):
                return True
    return False


def bounds(rows, columns, mask, cap):
    matrix = [[bool(mask >> (columns * r + c) & 1) for c in range(columns)]
              for r in range(rows)]
    row_core = [r for r in range(rows) if not all(matrix[r])]
    col_core = [c for c in range(columns) if not all(matrix[r][c] for r in range(rows))]
    essential = sum(any(matrix[r][c] for c in col_core) for r in range(rows))
    essential += sum(any(matrix[r][c] for r in row_core) for c in range(columns))
    if cap >= essential:
        return None

    neighborhoods = [frozenset(c for c in col_core if matrix[r][c]) for r in row_core]
    if not any(a & b for a, b in combinations(set(neighborhoods), 2)):
        return None
    transposed = [frozenset(r for r in row_core if matrix[r][c]) for c in col_core]
    leaves = rows + columns - sum(not s for s in neighborhoods + transposed)
    exact = leaves == essential and (can_split(neighborhoods) or can_split(transposed))
    return essential, exact


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("catalog", type=Path)
    args = parser.parse_args()
    data = json.loads(args.catalog.read_text(encoding="utf-8"))
    count = 0
    exact_count = 0
    for item in data["gaps"]:
        if item.get("weight", 0) <= 1 or item.get("pr_open") or not item.get("offerable_now"):
            continue
        statement = item.get("statement", "")
        if not statement.startswith("PEqualNP.Represents.RepSizeAtMost"):
            continue
        match = MASK_STATEMENT.search(statement)
        dimensions = re.findall(r"Fin (\d+)", statement)
        if not match or not dimensions:
            continue
        mask, columns, cap = map(int, match.groups())
        rows = int(dimensions[0])
        if not 0 < rows * columns <= 150:
            continue
        result = bounds(rows, columns, mask, cap)
        if result is not None:
            lower, exact = result
            print(item["id"], rows, columns, mask, cap, lower, "exact" if exact else "lower bound")
            count += 1
            exact_count += exact
    print(data["desk_read_at"], count, "obstructions,", exact_count, "matching upper bounds")


if __name__ == "__main__":
    main()
