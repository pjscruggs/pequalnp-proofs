"""Replay two exact one-hot monotone circuit costs using truth-table DP."""

import argparse
from dataclasses import dataclass
from functools import lru_cache


@dataclass(frozen=True)
class Case:
    gap: int
    mask: int
    core: tuple
    deletions: tuple
    gates: tuple


CASES = (
    Case(
        23742,
        842943,
        (4, 4, 0x35AF),
        (("column", 5), ("column", 3), ("row", 0)),
        (
            ("or", 6, 7), ("or", 8, 9),
            ("or", 5, 11), ("and", 1, 12),
            ("or", 4, 10), ("and", 2, 14),
            ("or", 4, 5), ("and", 3, 16),
            ("or", 0, 13), ("or", 18, 15), ("or", 19, 17),
        ),
    ),
    Case(
        23705,
        839029,
        (3, 5, 3477),
        (("column", 5), ("row", 1), ("column", 4)),
        (
            ("or", 0, 1), ("or", 8, 9),
            ("or", 4, 6), ("or", 12, 11), ("and", 10, 13),
            ("or", 6, 7), ("and", 2, 15),
            ("or", 4, 5), ("and", 3, 17),
            ("or", 14, 16), ("or", 19, 18),
        ),
    ),
)


def input_tables(rows, columns):
    row_stars = tuple(((1 << columns) - 1) << (columns * row) for row in range(rows))
    column_stars = tuple(
        sum(1 << (columns * row + column) for row in range(rows))
        for column in range(columns)
    )
    return row_stars + column_stars


def essential_inputs(mask, tables, cells):
    positives = [i for i in range(cells) if mask >> i & 1]
    negatives = [i for i in range(cells) if not (mask >> i & 1)]
    essential = set()
    for pos in positives:
        for neg in negatives:
            diff = [
                i for i, leaf in enumerate(tables)
                if leaf >> pos & 1 and not (leaf >> neg & 1)
            ]
            if len(diff) == 1:
                essential.add(diff[0])
    return essential


def project(mask, rows, columns):
    return sum(
        (mask >> (6 * row + column) & 1) << (len(columns) * i + j)
        for i, row in enumerate(rows)
        for j, column in enumerate(columns)
    )


def check_reductions(case):
    rows, columns = list(range(4)), list(range(6))
    for step, (shore, label) in enumerate(case.deletions):
        current = project(case.mask, rows, columns)
        tables = input_tables(len(rows), len(columns))
        wire = rows.index(label) if shore == "row" else len(rows) + columns.index(label)
        assert wire in essential_inputs(current, tables, len(rows) * len(columns))
        labels = rows if shore == "row" else columns
        labels.remove(label)
        restricted = project(case.mask, rows, columns)
        assert 0 < restricted < (1 << (len(rows) * len(columns))) - 1
        if step == 1:
            assert (len(rows), len(columns), restricted) == case.core
    assert (len(rows), len(columns)) == (3, 4)
    if case.gap == 23742:
        expected_path = [(0, 3), (0, 1), (2, 1), (2, 0), (1, 0), (1, 2)]
    else:
        expected_path = [(1, 3), (1, 2), (0, 2), (0, 0), (2, 0), (2, 1)]
    assert restricted == sum(1 << (4 * row + col) for row, col in expected_path)
    print(f"  Three essential-input restrictions leave the seven-vertex path (mask {restricted}).")


def check_witness(case):
    wires = list(input_tables(4, 6))
    assert len(case.gates) == 11
    for op, a, b in case.gates:
        assert 0 <= a < len(wires) and 0 <= b < len(wires)
        assert op in ("and", "or")
        wires.append(wires[a] & wires[b] if op == "and" else wires[a] | wires[b])
    assert wires[-1] == case.mask
    print("  Explicit eleven-gate witness matches all 24 cells.")


def submasks(mask):
    subset = mask
    while subset:
        yield subset
        subset = (subset - 1) & mask


def read_once(leaves):
    """Return the tables of binary AND/OR formulas using each leaf once."""

    @lru_cache(None)
    def tables(mask):
        pivot = mask & -mask
        if pivot == mask:
            return {leaves[pivot.bit_length() - 1]}
        results = set()
        for left in submasks(mask ^ pivot):
            right = mask ^ left
            for a in tables(left):
                for b in tables(right):
                    results.update((a & b, a | b))
        return results

    result = tables((1 << len(leaves)) - 1)
    tables.cache_clear()
    return result


def check_core(case):
    rows, columns, target = case.core
    tables = input_tables(rows, columns)
    support = (1 << len(tables)) - 1
    assert len(tables) == 8
    assert essential_inputs(target, tables, rows * columns) == set(range(len(tables)))
    assert target not in read_once(tables)
    tested = 0
    for shared in submasks(support):
        inside = tuple(table for i, table in enumerate(tables) if shared >> i & 1)
        outside = tuple(table for i, table in enumerate(tables) if not (shared >> i & 1))
        for repeated in read_once(inside):
            tested += 1
            assert target not in read_once(outside + (repeated, repeated)), (shared, repeated)
    print(f"  Core has no seven-gate tree or eight-gate DAG across {tested:,} shared-wire cases.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--gap", type=int, choices=[case.gap for case in CASES])
    parser.add_argument("--skip-dp", action="store_true", help="Check only reductions and witnesses.")
    args = parser.parse_args()
    for case in CASES:
        if args.gap is not None and case.gap != args.gap:
            continue
        print(f"L-meta-{case.gap}, mask {case.mask}")
        check_reductions(case)
        check_witness(case)
        if not args.skip_dp:
            check_core(case)


if __name__ == "__main__":
    main()
