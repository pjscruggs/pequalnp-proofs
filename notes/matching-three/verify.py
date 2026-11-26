"""Check the 14-gate witness and rerun the cap-13 monotone exclusion."""

from itertools import permutations
from pathlib import Path
import re
import subprocess
import sys


def witness():
    gates = []

    def append(op, a, b):
        gates.append((op, a, b))
        return 8 + len(gates)

    branches = []
    for column in range(3):
        left, right = [i for i in range(3) if i != column]
        a = append("AND", 3 + left, 6 + right)
        b = append("AND", 3 + right, 6 + left)
        branches.append(append("AND", column, append("OR", a, b)))
    out = append("OR", branches[0], branches[1])
    append("OR", out, branches[2])
    return gates


def check_witness():
    gates = witness()
    assert len(gates) == 14
    for mask in range(1 << 9):
        values = [bool(mask & (1 << i)) for i in range(9)]
        expected = any(all(values[3 * row + col] for row, col in enumerate(p))
                       for p in permutations(range(3)))
        for op, a, b in gates:
            assert a < len(values) and b < len(values)
            values.append(values[a] and values[b] if op == "AND" else values[a] or values[b])
        assert values[-1] == expected, mask
    print("14-gate circuit agrees on all 512 input graphs")


check_witness()
minimum_positive = [
    sum(1 << (3 * row + col) for row, col in enumerate(p))
    for p in permutations(range(3))
]
negative = [mask for mask in range(512)
            if all(mask & term != term for term in minimum_positive)]
maximum_negative = [mask for mask in negative
                    if not any(mask != other and mask & other == mask for other in negative)]
rows = minimum_positive + maximum_negative
assert len(rows) == 21
input_words = sorted(
    sum(1 << index for index, mask in enumerate(rows) if mask >> pin & 1)
    for pin in range(9)
)
source = Path(__file__).with_name("matching-shard.cpp").read_text(encoding="utf-8")
words = re.search(r"Frontier initial\{(\d+(?:,\d+)*)\}", source)[1]
assert input_words == sorted(map(int, words.split(",")))
run = subprocess.run(
    [str(Path(sys.argv[1]).resolve()), "13", "0", "2000000"],
    capture_output=True, text=True, check=True,
)
assert run.stdout.strip().endswith("EXHAUSTED 602209"), (run.stdout, run.stderr)
print(run.stdout.strip())
