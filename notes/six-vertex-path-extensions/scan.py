"""Find monotone one-a-side mask statements that reduce to a six- or seven-vertex path."""

import argparse
import json
import re
from pathlib import Path

STATEMENT = re.compile(
    r"PEqualNP\.Represents\.RepSizeAtMost "
    r"\(fun (?:u v : Fin (?P<square>\d+)|\(u : Fin (?P<rows>\d+)\) "
    r"\(v : Fin (?P<columns>\d+)\)) => "
    r"\((?P<mask>\d+) : ℕ\)\.testBit "
    r"\((?P<stride>\d+) \* u\.val \+ v\.val\)\) (?P<cap>\d+)"
)


def reduces_to_path(rows, columns, mask, vertices):
    table = [[bool(mask >> (r * columns + c) & 1) for c in range(columns)]
             for r in range(rows)]
    nonfull_rows = [row for row in table if not all(row)]
    nonfull_columns = [c for c in range(columns) if not all(row[c] for row in table)]
    distinct_rows = sorted(set(tuple(row[c] for c in nonfull_columns) for row in nonfull_rows))
    distinct_columns = sorted(set(zip(*distinct_rows)))
    row_count = len(distinct_rows)
    if sorted((row_count, len(distinct_columns))) != [vertices // 2, (vertices + 1) // 2]:
        return False

    adjacency = [set() for _ in range(vertices)]
    for c, column in enumerate(distinct_columns, row_count):
        for r, joined in enumerate(column):
            if joined:
                adjacency[r].add(c)
                adjacency[c].add(r)

    if sorted(map(len, adjacency)) != [1, 1] + [2] * (vertices - 2):
        return False

    reached = {0}
    while True:
        enlarged = reached.union(*(adjacency[v] for v in reached))
        if enlarged == reached:
            return len(reached) == vertices
        reached = enlarged


def iter_matches(data, vertices):
    for item in data["gaps"]:
        match = STATEMENT.fullmatch(item.get("statement", ""))
        if not match:
            continue
        rows = int(match["square"] or match["rows"])
        columns = int(match["square"] or match["columns"])
        if columns != int(match["stride"]):
            continue
        mask = int(match["mask"])
        if reduces_to_path(rows, columns, mask, vertices):
            optimum = rows + columns + 1
            yield item["id"], rows, columns, mask, int(match["cap"]), optimum, bool(item.get("offerable_now"))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("catalog", type=Path)
    parser.add_argument("--vertices", type=int, choices=(6, 7), required=True)
    args = parser.parse_args()
    data = json.loads(args.catalog.read_text(encoding="utf-8"))
    print("desk_id\trows\tcolumns\tmask\tposted_cap\toptimum\tofferable")
    for match in iter_matches(data, args.vertices):
        print(*match, sep="\t")


if __name__ == "__main__":
    main()
