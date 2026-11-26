"""Replay each signed witness on all 25 one-a-side inputs."""

import csv
from pathlib import Path


def replay(row):
    mask = int(row['mask'])
    gates = [gate.split(':') for gate in row['gates'].split(';')]
    assert len(gates) <= int(row['monotone_cap']), row['gap']
    assert any(op == 'not' for op, *_ in gates), row['gap']
    for left in range(5):
        for right in range(5):
            wires = [i in (left, 5 + right) for i in range(10)]
            for op, *operands in gates:
                pins = [int(pin) for pin in operands]
                assert all(0 <= pin < len(wires) for pin in pins), row['gap']
                if op == 'not':
                    (pin,) = pins
                    wires.append(not wires[pin])
                else:
                    assert op in ('and', 'or'), row['gap']
                    a, b = (wires[pin] for pin in pins)
                    wires.append((a and b) if op == 'and' else (a or b))
            assert wires[-1] == bool((mask >> (5 * left + right)) & 1), (row['gap'], left, right)

    if row['induced_path_at_read_once_cap'] == 'yes':
        table = [[(mask >> (5 * r + c)) & 1 for c in range(5)] for r in range(5)]
        active_rows = sum(map(any, table))
        active_cols = sum(map(any, zip(*table)))
        assert active_rows < 5 and active_cols < 5
        assert active_rows + active_cols - 1 == int(row['monotone_cap'])
        assert any(table[a][c] + table[a][d] + table[b][c] + table[b][d] == 3
                   for a in range(5) for b in range(a + 1, 5)
                   for c in range(5) for d in range(c + 1, 5))


if __name__ == '__main__':
    with Path(__file__).with_name('witnesses.tsv').open(newline='', encoding='utf-8') as source:
        rows = list(csv.DictReader(source, delimiter='\t'))
    assert len(rows) == len({row['gap'] for row in rows}) == 54
    for row in rows:
        replay(row)
    print('Verified all 54 signed circuits on all 25 promised inputs each.')
    print(sum(row['induced_path_at_read_once_cap'] == 'yes' for row in rows), 'induced-path certificates verified.')
