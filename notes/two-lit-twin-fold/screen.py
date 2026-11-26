"""Find six-point desk targets whose bounds transfer from five-point tables."""

import argparse
import json
import re
from itertools import combinations, combinations_with_replacement
from pathlib import Path

from replay import entry

TITLE = re.compile(r"graph H on 6 points with mask (\d+).*?AND/OR/NOT.*?at most (\d+) gates")


def reductions(mask):
    for keep, remove in combinations(range(6), 2):
        if any(entry(mask, 6, k, keep) != entry(mask, 6, k, remove) for k in range(6)):
            continue
        if not any(k not in (keep, remove) and entry(mask, 6, k, k) != entry(mask, 6, k, remove)
                   for k in range(6)):
            continue
        points = [k for k in range(6) if k != remove]
        quotient = sum(entry(mask, 6, a, b) << pos
                       for pos, (a, b) in enumerate(combinations_with_replacement(points, 2)))
        yield keep, remove, quotient


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("board", type=Path)
    parser.add_argument("atlas", type=Path)
    args = parser.parse_args()
    costs = dict(tuple(map(int, line.split())) for line in args.atlas.read_text().splitlines())
    print("gap\tmask\tcap\tkeep\tremove\tcore\tmin_size_lower_bound\tofferable\tverdict")
    for gap in json.loads(args.board.read_text(encoding="utf-8-sig"))["gaps"]:
        match = TITLE.search(gap["title"])
        if not match:
            continue
        mask, cap = map(int, match.groups())
        for keep, remove, core in reductions(mask):
            # The necessity witness ensures the quotient is nonconstant.
            assert core not in (0, (1 << 15) - 1)
            minimum = 1 + costs.get(core, 7)
            verdict = "excluded" if minimum > cap else "feasible" if core in costs else "unknown"
            print(gap["id"], mask, cap, keep, remove, core, minimum,
                  bool(gap["offerable"]), verdict, sep="\t")
            break


if __name__ == "__main__":
    main()
