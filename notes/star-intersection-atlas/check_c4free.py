"""Check the unique four-intersection candidate on a 4-cycle-free 5 x 6 grid."""
from itertools import combinations, permutations
from pathlib import Path

from check_atlas import evaluate
from check_obstruction import ROWS


def column_sets():
    pairs = list(combinations(range(5), 2))
    pair_masks = [sum(1 << k for k, (a, b) in enumerate(pairs)
                      if (col >> a) & (col >> b) & 1) for col in range(32)]

    def extend(columns, start, occupied):
        if len(columns) == 6:
            yield columns
            return
        for col in range(start, 32):
            if not occupied & pair_masks[col]:
                yield from extend(columns + (col,), col + 1, occupied | pair_masks[col])

    return extend((), 0, 0)


def orbit(columns, maps):
    return {tuple(sorted(mapping[col] for col in columns)) for mapping in maps}


def check():
    maps = [[sum(((col >> old) & 1) << new for new, old in enumerate(perm))
             for col in range(32)] for perm in permutations(range(5))]
    seen, representatives = set(), set()
    for columns in column_sets():
        if columns not in seen:
            representatives.add(columns)
            seen.update(orbit(columns, maps))
    exceptional = tuple(sum(((row >> j) & 1) << i for i, row in enumerate(ROWS))
                        for j in range(6))
    representatives.remove(min(orbit(exceptional, maps)))
    checked = 0
    for line in Path(__file__).with_name("c4free5x6.txt").read_text().splitlines():
        key, circuit = line.split(":")
        columns = tuple(map(int, key.split(",")))
        selectors = [int(s, 16) for s in circuit.split()]
        graph = sum(((col >> i) & 1) << (6*i+j) for j, col in enumerate(columns)
                    for i in range(5))
        representatives.remove(columns)
        if len(selectors) != 7 or evaluate(5, 6, selectors) != graph:
            raise ValueError(f"invalid witness for {columns}")
        checked += 1
    if representatives:
        raise ValueError("representatives without a witness")
    print(f"{len(seen)} distinct column sets, {checked} verified orbits plus the obstruction")


if __name__ == "__main__":
    check()
