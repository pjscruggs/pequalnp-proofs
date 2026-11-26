"""Verify the quotient, gate counts, and signed witnesses for the listed masks."""
import csv
from collections import Counter
from pathlib import Path

from staircase_core import CELLS, TARGET, profile


def table_types(lines):
    return sorted(Counter(lines).items(), key=lambda item: sum(item[0]))


def lift(costs, rows, cols):
    return min(cost + sum(n - 1 for i, n in enumerate(rows) if i != row_default)
                    + sum(n - 1 for i, n in enumerate(cols) if i != col_default)
               for (row_default, col_default), cost in costs.items())


def check(record, monotone, signed):
    mask = int(record['mask'])
    table = tuple(tuple(mask >> (5 * r + c) & 1 for c in range(5)) for r in range(5))
    transpose = tuple(zip(*table))
    rows, cols = table_types(table), table_types(transpose)
    assert len(rows) == len(cols) == 3
    a = [table.index(line) for line, _ in rows]
    b = [transpose.index(line) for line, _ in cols]
    assert sum(table[a[r]][b[c]] << (3 * r + c) for r, c in CELLS) == TARGET
    row_sizes = tuple(count for _, count in rows)
    col_sizes = tuple(count for _, count in cols)
    assert row_sizes == tuple(map(int, record['row_weights'].split(',')))
    assert col_sizes == tuple(map(int, record['column_weights'].split(',')))
    assert lift(monotone, row_sizes, col_sizes) == int(record['monotone_size'])
    size = lift(signed, row_sizes, col_sizes)
    assert size == int(record['signed_size'])

    gates = [gate.split(':') for gate in record['gates'].split(';')]
    assert len(gates) == size
    for left in range(5):
        for right in range(5):
            wires = [i in (left, 5 + right) for i in range(10)]
            for op, *operand_text in gates:
                operands = tuple(map(int, operand_text))
                assert all(0 <= p < len(wires) for p in operands)
                if op == 'not':
                    (u,) = operands
                    wires.append(not wires[u])
                else:
                    assert op in ('and', 'or')
                    u, v = operands
                    wires.append(wires[u] and wires[v] if op == 'and' else wires[u] or wires[v])
            assert wires[-1] == bool(table[left][right]), (record['gap'], left, right)


if __name__ == '__main__':
    mono, signed = profile(False), profile(True)
    with Path(__file__).with_name('cases.tsv').open(encoding='utf8', newline='') as source:
        rows = list(csv.DictReader(source, delimiter='\t'))
    assert len(rows) == len({row['gap'] for row in rows}) == 13
    for row in rows:
        check(row, mono, signed)
    print('Verified 13 weighted quotients and 325 signed circuit evaluations.')
