"""Verify the quotient formulas and promised outputs for the published examples."""
import csv
from pathlib import Path

from core_profile import profile
from profile_screen import FAMILIES, closed_forms, min_cost, quotient


def evaluate(gates, left, right):
    wires = [pin in (left, 5 + right) for pin in range(10)]
    for gate in gates:
        op, *pins = gate.split(':')
        weights = [int(pin) for pin in pins]
        assert all(0 <= pin < len(wires) for pin in weights)
        if op == 'not':
            (a,) = weights
            wires.append(not wires[a])
        else:
            assert op in ('and', 'or')
            a, b = weights
            wires.append(wires[a] and wires[b] if op == 'and' else wires[a] or wires[b])
    return wires[-1]


def check(row, costs):
    mask = int(row['mask'])
    family, a, b = quotient(mask)
    assert family == row['family']
    assert a == tuple(map(int, row['rows'].split(',')))
    assert b == tuple(map(int, row['cols'].split(',')))
    optimum = tuple(min_cost(table, a, b) for table in costs[family])
    assert optimum == closed_forms(family, a, b) == (int(row['monotone']), int(row['signed']))
    gates = row['gates'].split(';')
    assert len(gates) == optimum[1]
    for left in range(5):
        for right in range(5):
            assert evaluate(gates, left, right) == bool(mask >> (5 * left + right) & 1)


if __name__ == '__main__':
    profiles = {family: tuple(profile(sum(n << (3 * i) for i, n in enumerate(masks)), signed)
                              for signed in (False, True))
                for family, masks in FAMILIES.items()}
    with Path(__file__).with_name('examples.tsv').open(encoding='utf8', newline='') as inp:
        rows = list(csv.DictReader(inp, delimiter='\t'))
    assert len(rows) == len({r['gap'] for r in rows}) == 22
    for row in rows:
        check(row, profiles)
    print('Verified 22 weighted quotient formulas and all 550 promised signed circuit outputs.')
