"""Replay full-table witnesses and check the weighted omission predictions."""
import argparse
import csv
from collections import Counter
from itertools import permutations, product
from pathlib import Path

from frontier import reachable

CORE_ROWS = (1, 2, 3, 4)
CORE = sum(mask << (3 * row) for row, mask in enumerate(CORE_ROWS))
CRITICAL = {(-1, -1), (0, -1), (-1, 1), (0, 1), (3, -1), (-1, 2), (3, 2)}


def records(name):
    with Path(__file__).with_name(name).open(encoding='utf8', newline='') as source:
        return list(csv.DictReader(source, delimiter='\t'))


def evaluate(code, inputs):
    signals = inputs.copy()
    for gate in code.split(';'):
        op, *operand_text = gate.split(':')
        pins = [int(token) for token in operand_text]
        assert all(0 <= pin < len(signals) for pin in pins)
        if op == 'not':
            (a,) = pins
            signals.append(not signals[a])
        else:
            assert op in ('and', 'or')
            a, b = pins
            signals.append(signals[a] and signals[b] if op == 'and' else signals[a] or signals[b])
    return signals[-1]


def core_costs(check_all, check_critical):
    costs = {}
    for row in records('profile.tsv'):
        signed = row['basis'] == 'signed'
        r, c, size = (int(row[key]) for key in ('omitted_row', 'omitted_col', 'size'))
        assert (signed, r, c) not in costs
        costs[signed, r, c] = size
        assert len(row['gates'].split(';')) == size
        for i, j in product(range(4), range(3)):
            inputs = [x == i for x in range(4) if x != r] + [x == j for x in range(3) if x != c]
            assert evaluate(row['gates'], inputs) == bool(CORE >> (3 * i + j) & 1)
        if check_all or (check_critical and signed and (r, c) in CRITICAL):
            assert not reachable(CORE, r, c, signed, size - 1), (signed, r, c, size)
            print('Excluded core budget', signed, r, c, size - 1, flush=True)
    assert len(costs) == 21
    return costs


def quotient(mask):
    physical = tuple(tuple(mask >> (5 * r + c) & 1 for c in range(5)) for r in range(5))
    transpose = tuple(zip(*physical))
    rows, cols = Counter(physical), Counter(transpose)
    for representatives in permutations(rows):
        for column_types in permutations(cols):
            order = [transpose.index(c) for c in column_types]
            quotient_rows = tuple(sum(r[x] << i for i, x in enumerate(order)) for r in representatives)
            if quotient_rows == CORE_ROWS:
                return [rows[r] for r in representatives], [cols[c] for c in column_types]
    raise ValueError(f'Mask {mask} has a different core')


def check_example(row, costs):
    mask = int(row['mask'])
    a, b = quotient(mask)
    assert a == list(map(int, row['rows'].split(',')))
    assert b == list(map(int, row['cols'].split(',')))

    def lift(r, c):
        return (sum(size - 1 for i, size in enumerate(a) if i != r)
                + sum(size - 1 for i, size in enumerate(b) if i != c))

    choices = tuple(product(range(-1, 4), range(-1, 3)))
    signed = min(costs[True, r, c] + lift(r, c) for r, c in choices)
    separate = min(costs[True, r, -1] + costs[True, -1, c] - costs[True, -1, -1] + lift(r, c)
                   for r, c in choices)
    assert costs[False, -1, -1] + lift(-1, -1) == int(row['monotone'])
    assert signed == int(row['signed']) == len(row['gates'].split(';'))
    assert separate == int(row['separate_penalty_prediction'])
    for i, j in product(range(5), repeat=2):
        inputs = [x in (i, 5 + j) for x in range(10)]
        assert evaluate(row['gates'], inputs) == bool(mask >> (5 * i + j) & 1)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--critical-exclusions', action='store_true')
    parser.add_argument('--all-exclusions', action='store_true')
    args = parser.parse_args()
    costs = core_costs(args.all_exclusions, args.critical_exclusions)
    rows = records('examples.tsv')
    assert len({r['id'] for r in rows}) == len(rows) == 7
    for row in rows:
        check_example(row, costs)
    print('Replayed 21 core witnesses, seven weighted formulas and seven signed gate lists.')
