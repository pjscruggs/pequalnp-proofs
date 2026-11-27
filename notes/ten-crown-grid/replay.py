"""Rebuild the grid-decoder search with Python 3.10+ and a C++20 compiler."""
from itertools import combinations, permutations, product
from pathlib import Path
from tempfile import TemporaryDirectory
import os
import subprocess


SOURCE = Path(__file__).resolve().parent
CELLS = [(i, i) for i in range(10)] + list(combinations(range(10), 2))
POS = {cell: i for i, cell in enumerate(CELLS)}
CODES = [1 << r | 1 << (3 + c) for c in range(3) for r in range(3)] + [64]
RECTANGLE = [1 << r | 1 << (2 + c) for r in range(2) for c in range(5)]
FULL = (1 << 55) - 1


def symmetries(square):
    height, width = (3, 3) if square else (2, 5)
    for rows, cols, flip in product(permutations(range(height)), permutations(range(width)),
                                    range(2 if square else 1)):
        if square:
            labels = [(3 * rows[i % 3] + cols[i // 3] if flip else
                       3 * cols[i // 3] + rows[i % 3]) for i in range(9)] + [9]
        else:
            labels = [5 * rows[i // 5] + cols[i % 5] for i in range(10)]
        yield [1 << POS[tuple(sorted((labels[a], labels[b])))] for a, b in CELLS]


def prefix_representatives(inputs, max_cost, square):
    maps = list(symmetries(square))
    seen = set(inputs) | {0, FULL}
    layers = [set(inputs)]
    for cost in range(1, max_cost + 1):
        layer = set()
        for i in range((cost - 1) // 2 + 1):
            for a, b in product(layers[i], layers[cost - 1 - i]):
                layer.update((a & b, a | b))
        layer -= seen
        seen.update(layer)
        layers.append(layer)
        unvisited = layer.copy()
        reps = []
        while unvisited:
            word = min(unvisited)
            bits = [i for i in range(55) if word & (1 << i)]
            orbit = {sum(p[i] for i in bits) for p in maps}
            assert orbit <= layer
            unvisited -= orbit
            reps.append(word)
        yield cost, len(layer), reps


def run(*argv):
    return subprocess.check_output(argv, text=True)


def verify_control(result):
    gates = [tuple(map(int, triple.split(','))) for triple in result.split()[5:]]
    assert len(gates) <= 12
    for a, b in product(range(10), repeat=2):
        wires = [bool((CODES[a] | CODES[b]) & (1 << j)) for j in range(7)]
        for op, x, y in gates:
            assert op in (0, 1) and 0 <= x < len(wires) and 0 <= y < len(wires)
            wires.append(wires[x] or wires[y] if op else wires[x] and wires[y])
        assert wires[-1] == (a != b)


def main(work):
    formula, reverse = [work / (name + '.exe') for name in ('formula', 'reverse')]
    for binary in (formula, reverse):
        subprocess.run([os.environ.get('CXX', 'g++'), '-O3', '-std=c++20',
                        SOURCE / (binary.stem + '.cpp'), '-o', binary], check=True)
    check_grid(work, formula, reverse, square=True)
    check_grid(work, formula, reverse, square=False)


def check_grid(work, formula, reverse, square):
    codes, cap = (CODES, 11) if square else (RECTANGLE, 10)
    inputs = [sum(1 << i for i, (a, b) in enumerate(CELLS)
                  if (codes[a] | codes[b]) & (1 << j)) for j in range(7)]
    cases = work / 'grid.txt'
    cases.write_text(f'grid 7 {cap} ' + ' '.join(map(str, codes)) + '\n')
    assert run(formula, cases, '3000000', '5', '0').split()[4] == 'exhausted'
    if square:
        control = run(formula, cases, '3000000', '5', '1')
        assert control.split()[4] == 'found'
        verify_control(control)
        print('The 12-gate control passes all 100 ordered inputs.', flush=True)
    totals = ([(42, 6), (271, 20), (1531, 63), (6818, 198), (27698, 650)]
              if square else [(41, 5), (250, 12), (1305, 33), (5725, 90)])
    batch = work / 'prefix.txt'
    for cost, count, reps in prefix_representatives(inputs, len(totals), square):
        assert (count, len(reps)) == totals[cost - 1]
        batch.write_text(''.join(f'W_{i} 8 {cap-cost} ' +
                         ' '.join(map(str, inputs + [word])) + '\n'
                         for i, word in enumerate(reps)))
        lines = run(formula, batch, '3000000', '5', '0').splitlines()
        assert len(lines) == len(reps)
        assert all(line.split()[4] == 'exhausted' for line in lines)
        print(f'Prefix cost {cost}: excluded {len(reps)} orbits.', flush=True)
    lines = [line.split() for line in run(reverse, cases).splitlines()]
    assert len(lines) == 6
    compatible = (1, 0, 12, 61, 398, 1829) if square else (1, 0, 11, 55, 340, 1495)
    for i, (row, count) in enumerate(zip(lines, compatible)):
        assert row[:2] == ['suffix', str(i)] and row[4:10] == [
            'compatible', str(count), 'solved', '0', 'cutoffs', '0']
    print(f'Excluded all {sum(compatible):,} compatible suffix pairs at cap {cap}. No cutoffs.')


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Run without -O so all replay checks are enabled.')
    with TemporaryDirectory() as directory:
        main(Path(directory))
