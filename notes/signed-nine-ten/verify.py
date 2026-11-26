"""Replay finite exclusions and check witness circuits with a scalar evaluator."""

import json
from pathlib import Path
import re
import subprocess
import sys


HERE = Path(__file__).resolve().parent
SOLVER = Path(sys.argv[1]).resolve()


def expected(mask, points, i, j):
    return bool(mask >> (points * min(i, j) + max(i, j)) & 1)


def check_circuit(points, mask, gates, output):
    for index, (operation, a, b) in enumerate(gates, start=points):
        assert operation in (0, 1, 2) and 0 <= a < index and 0 <= b < index
    assert 0 <= output < points + len(gates)
    for i in range(points):
        for j in range(points):
            wires = [k in (i, j) for k in range(points)]
            for operation, a, b in gates:
                wires.append((wires[a] and wires[b], wires[a] or wires[b], not wires[a])[operation])
            assert wires[output] == expected(mask, points, i, j)


def search(unit, points, mask, cap):
    return subprocess.run(
        [str(SOLVER), "6000000"], input=f"{unit} {points} {mask} {cap}\n",
        capture_output=True, text=True, check=True,
    )


def check_exclusion(unit, points, mask, cap):
    run = search(unit, points, mask, cap)
    assert not run.stdout and re.fullmatch(rf"{unit} UNSAT [0-9]+\s*", run.stderr), run


def check_quotient(unit, mask, size):
    classes = {}
    for i in range(6):
        profile = tuple(expected(mask, 6, i, j) for j in range(6))
        classes.setdefault(profile, []).append(i)
    reps = [values[0] for values in classes.values()]
    points = len(reps)
    if points == 6:
        return 0
    for values in classes.values():
        for clone in values[1:]:
            assert any(expected(mask, 6, i, i) != expected(mask, 6, i, clone) for i in reps)
    quotient = sum(
        int(expected(mask, 6, a, b)) << (points * i + j)
        for i, a in enumerate(reps)
        for j, b in enumerate(reps)
        if i <= j
    )
    lower = size - (6 - points)
    check_exclusion(unit, points, quotient, lower - 1)
    run = search(unit, points, quotient, lower)
    witness = re.fullmatch(
        rf"{unit} {points} {quotient} {lower} ([0-9, ]+) output ([0-9]+); calls [0-9]+\s*",
        run.stdout,
    )
    assert witness and not run.stderr, run
    gates = [tuple(map(int, gate.split(","))) for gate in witness[1].split()]
    assert len(gates) == lower
    check_circuit(points, quotient, gates, int(witness[2]))
    return 1


rows = json.loads((HERE / "witnesses.json").read_text(encoding="utf-8"))
assert len(rows) == len({row["id"] for row in rows}) == 54
assert sorted(row["posted_cap"] for row in rows) == [9] * 44 + [10] * 10
quotients = 0
for row in rows:
    unit, mask, cap = row["id"], row["mask"], row["posted_cap"]
    gates = row["gates"]
    assert len(gates) == cap + 1
    check_circuit(6, mask, gates, row["output"])
    check_exclusion(unit, 6, mask, cap)
    quotients += check_quotient(unit, mask, len(gates))
assert quotients == 13
print(f"{len(rows)} exclusions and witnesses checked, including {quotients} exact twin quotients")
