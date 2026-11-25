"""Independently check the 14-cover exclusion by list-coloring the conflict graph.

Place next to the published affine_extension_cnf.py and run:
python3 affine_coloring_check.py --solver cadical --checker lrat-trim
"""

import argparse
from itertools import combinations
from pathlib import Path
import subprocess
import sys
import tempfile


def coloring(rows, fixed, budget=14):
    # Each vertex is a nonincident point-line pair. Two vertices can share a
    # rectangle iff both cross-pairs are also nonincident.
    vertices = [
        (p, l) for p, r in enumerate(rows) for l in range(21) if not (r >> l & 1)
    ]
    conflicts = [0] * len(vertices)
    for i, (p, l) in enumerate(vertices):
        for j in range(i):
            q, k = vertices[j]
            if (rows[p] >> k | rows[q] >> l) & 1:
                conflicts[i] |= 1 << j
                conflicts[j] |= 1 << i
    free = budget - len(fixed)
    keys, clauses = {}, []
    forced = []
    for i, (p, l) in enumerate(vertices):
        eligible = []
        for color, shape in enumerate(fixed):
            if p < 16 and not (shape >> p & 1):
                continue
            if any(shape >> q & rows[q] >> l & 1 for q in range(16)):
                continue
            eligible.append(color)
        if not eligible:
            forced.append(i)
        eligible.extend(range(len(fixed), budget))
        for color in eligible:
            keys[i, color] = len(keys) + 1
        clauses.append([keys[i, c] for c in eligible])
    for i, j in combinations(range(len(vertices)), 2):
        if conflicts[i] >> j & 1:
            for c in range(budget):
                if (i, c) in keys and (j, c) in keys:
                    clauses.append([-keys[i, c], -keys[j, c]])
    # A clique of vertices excluded from every fixed color must use distinct
    # free colors, which we may name in that order.
    choices = sum(1 << i for i in forced)

    def clique(T, k):
        if not k:
            return []
        while T.bit_count() >= k:
            one = T & -T
            i = one.bit_length() - 1
            T ^= one
            tail = clique(T & conflicts[i], k - 1)
            if tail is not None:
                return [i] + tail

    anchor = next(
        s for k in reversed(range(free + 1)) if (s := clique(choices, k)) is not None
    )
    for j, i in enumerate(anchor):
        clauses.append([keys[i, len(fixed) + j]])
    return len(keys), clauses, len(anchor)


def run(note, save, solver, checker):
    sys.path.insert(0, str(note))
    from affine_extension_cnf import orbits, ROWS, SHAPES

    save.mkdir(parents=True, exist_ok=True)
    for relaxed, size in [((), 1), *orbits(3)]:
        budget = 14 if relaxed else 15
        n, clauses, anchors = coloring(
            ROWS, [s for i, s in enumerate(SHAPES) if i not in relaxed], budget
        )
        f = save / ("color" + "_".join(map(str, relaxed)) + ".cnf")
        with f.open("w", encoding="ascii") as out:
            print("p cnf", n, len(clauses), file=out)
            for clause in clauses:
                print(*clause, 0, file=out)
        if solver:
            proof = save / (f.stem + ".lrat")
            args = [solver, "-q", "-n"]
            args += ["--lrat", str(f), str(proof)] if relaxed else [str(f)]
            result = subprocess.run(args, capture_output=True, text=True)
            code, marker = (20, "s UNSATISFIABLE") if relaxed else (10, "s SATISFIABLE")
            if result.returncode != code or marker not in result.stdout.splitlines():
                raise RuntimeError(result.stdout + result.stderr)
            if relaxed:
                checked = subprocess.run(
                    [checker, str(f), str(proof)], capture_output=True, text=True
                )
                if (
                    checked.returncode != 20
                    or "s VERIFIED" not in checked.stdout.splitlines()
                ):
                    raise RuntimeError(checked.stdout + checked.stderr)
                proof.unlink()
            print(
                relaxed,
                marker,
                "LRAT verified" if relaxed else "positive control",
                flush=True,
            )
        else:
            print(relaxed, n, len(clauses), anchors, f, flush=True)


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--notes", type=Path, default=Path(__file__).resolve().parent)
    p.add_argument(
        "--emit", type=Path, help="only generate the DIMACS files into this directory"
    )
    p.add_argument("--solver", default="cadical")
    p.add_argument("--checker", default="lrat-trim")
    args = p.parse_args()
    if args.emit:
        run(args.notes.resolve(), args.emit.resolve(), None, None)
    else:
        with tempfile.TemporaryDirectory() as tmp:
            run(args.notes.resolve(), Path(tmp), args.solver, args.checker)
