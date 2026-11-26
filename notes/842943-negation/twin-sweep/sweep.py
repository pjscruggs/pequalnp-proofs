"""Check posted 4-by-6 gate caps using two essential duplicate columns."""

import argparse
import csv
import itertools
import json
import re
import subprocess
from collections import Counter
from functools import cache
from pathlib import Path


ROOT = Path(__file__).resolve().parent
CHECKED_REVISION = "7e46f41504f47cca795d80ac554db9bdf8baa454"
PATH_SWEEP_REVISION = "a92151c18085dd4e96a72abc15d4ad61b14b7344"
CAP = re.compile(
    r"One-a-side promise: the 4 by 6 bipartite graph with mask (\d+)"
    r" has a fan-in-two AND/OR circuit of at most (\d+) gates"
)
CORE_EXCLUSION = re.compile(
    r"¬\s+PEqualNP\.Represents\.RepSizeAtMost\s+\(fun\s+"
    r"(?:\w+\s+\w+\s*:\s*Fin 4|\(\w+\s*:\s*Fin 4\)\s*\(\w+\s*:\s*Fin 4\))"
    r"\s*=>\s*\((\d+)\s*:\s*[ℕ\w]+\)\.testBit\s*"
    r"\(4\s*\*\s*\w+\.val\s*\+\s*\w+\.val\)\)\s*(\d+)"
)
PERMUTATIONS = tuple(itertools.permutations(range(4)))


def git(repo, *args):
    return subprocess.run(
        ["git", "-C", str(repo), *args], capture_output=True,
        encoding="utf-8", check=True,
    ).stdout


def matrix(mask, columns):
    return tuple(
        tuple((mask >> (columns * i + j)) & 1 for j in range(columns))
        for i in range(4)
    )


@cache
def canonical(mask):
    rows = matrix(mask, 4)
    return min(
        sum(grid[rs[i]][cs[j]] << (4 * i + j) for i in range(4) for j in range(4))
        for grid in (rows, tuple(zip(*rows)))
        for rs in PERMUTATIONS
        for cs in PERMUTATIONS
    )


def checked_exclusions(repo):
    lines = git(
        repo, "grep", "-n", "-F", "¬ PEqualNP.Represents.RepSizeAtMost",
        CHECKED_REVISION, "--", "lean/PEqualNP/Outside",
    )
    by_orbit = {}
    for line in lines.splitlines():
        _, path, number, source = line.split(":", 3)
        match = CORE_EXCLUSION.search(source)
        if not match:
            continue
        mask, excluded_cap = map(int, match.groups())
        if mask >= (1 << 16):
            raise ValueError(f"Mask is out of range in {path}")
        key = canonical(mask)
        candidate = excluded_cap + 1, mask, path, number
        if key not in by_orbit or candidate > by_orbit[key]:
            by_orbit[key] = candidate
    return by_orbit


def collapse(mask):
    columns = list(zip(*matrix(mask, 6)))
    representatives = list(dict.fromkeys(columns))
    if len(representatives) != 4:
        return None
    for column in representatives:
        if columns.count(column) == 1:
            continue
        if not any(
            column[i] and any(not other[i] for other in representatives)
            for i in range(4)
        ):
            return None
    return sum(
        representatives[j][i] << (4 * i + j)
        for i in range(4)
        for j in range(4)
    )


def scan(board, lower_bounds, path_ids):
    for gap in board["gaps"]:
        cap_match = CAP.fullmatch(gap["title"])
        if not cap_match or gap["kind"] != "prove":
            continue
        mask, cap = map(int, cap_match.groups())
        core = collapse(mask)
        if core is None:
            continue
        check = lower_bounds.get(canonical(core))
        if check is None:
            continue
        core_bound, checked_mask, check_path, line = check
        bound = core_bound + 2
        if bound > cap:
            yield (
                gap["id"], mask, cap, core, checked_mask, bound,
                check_path, line, int(gap["offerable"]), int(gap["id"] in path_ids),
            )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--board", type=Path, default=ROOT / "desk-board.json")
    parser.add_argument("--output", type=Path, default=ROOT / "results.tsv")
    args = parser.parse_args()
    board = json.loads(args.board.read_text(encoding="utf-8-sig"))
    path_targets = git(
        args.repo, "show", f"{PATH_SWEEP_REVISION}:notes/path-seven-extensions/targets.tsv",
    )
    path_ids = set(re.findall(r"L-meta-\d+", path_targets))
    lower_bounds = checked_exclusions(args.repo)
    excluded = list(scan(board, lower_bounds, path_ids))
    with args.output.open("w", encoding="utf-8", newline="") as out:
        writer = csv.writer(out, delimiter="\t", lineterminator="\n")
        writer.writerow((
            "desk_id", "mask", "posted_cap", "collapsed_mask", "checked_mask",
            "lower_bound", "checked_lean_file", "checked_line", "offerable",
            "in_published_path_sweep",
        ))
        writer.writerows(excluded)
    print(f"Desk board {board['updated_at']}, proof checkout {CHECKED_REVISION}")
    print(f"{len(lower_bounds)} checked 4-by-4 orbits in indexed theorem lines")
    print(f"{len(excluded)} excluded caps, across {len(set(row[4] for row in excluded))} core orbits")
    print(f"Gap between lower bound and posted cap: {dict(Counter(row[5] - row[2] for row in excluded))}")
    print(f"{sum(row[8] for row in excluded)} offerable")
    print(f"{sum(row[9] for row in excluded)} overlap with the published path sweep")
    print(f"{sum(row[8] and not row[9] for row in excluded)} offerable and outside the path sweep")


if __name__ == "__main__":
    main()
