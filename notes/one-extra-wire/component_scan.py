"""Find literal monotone mask caps first excluded by the repeated-wire bound."""
import argparse
import json
from pathlib import Path
import re

STATEMENT = re.compile(
    r"PEqualNP\.Represents\.RepSizeAtMost \(fun \(u : Fin (\d+)\) \(v : Fin (\d+)\)"
    r" => \((\d+) : ℕ\)\.testBit \((\d+) \* u\.val \+ v.val\)\) (\d+)"
)


def component_counts(left, right, mask):
    adjacent = {vertex: set() for vertex in range(left + right)}
    for r in range(left):
        for c in range(right):
            if (mask >> (r * right + c)) & 1:
                adjacent[r].add(left + c)
                adjacent[left + c].add(r)
    if any(len(neighbors) == (right if vertex < left else left)
           for vertex, neighbors in adjacent.items()):
        return None
    unseen = {vertex for vertex, neighbors in adjacent.items() if neighbors}
    essential = len(unseen)
    incomplete = 0
    while unseen:
        component = {unseen.pop()}
        frontier = list(component)
        while frontier:
            neighbors = adjacent[frontier.pop()] & unseen
            unseen.difference_update(neighbors)
            component.update(neighbors)
            frontier.extend(neighbors)
        rows = {v for v in component if v < left}
        edge_count = sum(len(adjacent[r]) for r in rows)
        incomplete += edge_count < len(rows) * (len(component) - len(rows))
    return essential, incomplete


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("catalog", type=Path)
    args = parser.parse_args()
    catalog = json.loads(args.catalog.read_text(encoding="utf-8"))
    scanned = 0
    large = 0
    for unit in catalog["gaps"]:
        match = STATEMENT.fullmatch(unit.get("statement", ""))
        if not match:
            continue
        rows, columns, mask, stride, cap = map(int, match.groups())
        if stride != columns:
            continue
        scanned += 1
        if min(rows, columns) < 6:
            continue
        large += 1
        counts = component_counts(rows, columns, mask)
        if counts is None:
            continue
        essential, incomplete = counts
        lower_bound = essential - 1 + (incomplete + 1) // 2
        if essential <= cap < lower_bound:
            print(unit["id"], rows, columns, mask, cap, lower_bound, incomplete,
                  "offerable" if unit.get("offerable_now") else "unavailable")
    print(catalog["desk_read_at"], scanned, "literal monotone mask statements,",
          large, "with both shores at least six")


if __name__ == "__main__":
    assert component_counts(4, 4, 19475) == (8, 2)
    assert component_counts(6, 6, 17986273347) == (12, 3)
    main()
