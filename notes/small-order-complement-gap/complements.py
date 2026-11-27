"""Enumerate the complement pairs on the square one-hot promise."""
import argparse
import csv
from pathlib import Path
import subprocess


def representatives(n):
    cells = range(n * n)
    # Transposition conjugates each adjacent row swap to a column swap.
    generators = [[(i % n) * n + i // n for i in cells]]
    for a in range(n - 1):
        rows = list(range(n))
        rows[a], rows[a + 1] = rows[a + 1], rows[a]
        generators.append([rows[i // n] * n + i % n for i in cells])
    orbit = {}
    for mask in range(1 << (n * n)):
        if mask in orbit:
            continue
        orbit[mask] = mask
        stack = [mask]
        while stack:
            value = stack.pop()
            for perm in generators:
                other = sum(((value >> i) & 1) << perm[i] for i in cells)
                if other not in orbit:
                    orbit[other] = mask
                    stack.append(other)
    return orbit


def check_witness(lines, n, mask, budget):
    gates = [line.split() for line in lines[:-1]]
    op, output = lines[-1].split()
    if op != "output" or len(gates) != budget:
        raise ValueError("unexpected witness length or output")
    for cell in range(n * n):
        row, col = divmod(cell, n)
        wires = [i == row for i in range(n)] + [j == col for j in range(n)]
        for kind, a, b in gates:
            i, j = int(a), int(b)
            if kind not in ("or", "and") or not (0 <= i < len(wires) and 0 <= j < len(wires)):
                raise ValueError("invalid gate")
            wires.append((wires[i] or wires[j]) if kind == "or" else (wires[i] and wires[j]))
        if not 0 <= int(output) < len(wires) or wires[int(output)] != bool(mask >> cell & 1):
            raise ValueError(f"incorrect output at cell {cell}")


def minimum(n, mask, solver):
    if mask == 0:
        return 0  # The output can point beyond the input array.
    if mask == (1 << (n * n)) - 1:
        return 1  # Empty AND; neither a raw pin nor a missing output suffices.
    for budget in range(12):
        lines = subprocess.check_output(
            [solver, str(n), str(n), str(mask), str(budget), "1500000"], text=True
        ).splitlines()
        verdict = lines[0].split()[0]
        if verdict == "SAT":
            check_witness(lines[1:], n, mask, budget)
            return budget
        if verdict != "UNSAT":
            raise RuntimeError(f"incomplete search at mask {mask}, budget {budget}")
    raise RuntimeError(f"minimum exceeds maximum search budget for {mask}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("side", type=int, choices=(3, 4))
    parser.add_argument("solver", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    n = args.side
    orbit = representatives(n)
    reps = sorted(set(orbit.values()))
    if len(reps) != {3: 26, 4: 192}[n]:
        raise ValueError("unexpected orbit count")
    costs = {mask: minimum(n, mask, args.solver.resolve()) for mask in reps}
    full = (1 << (n * n)) - 1
    gaps = [costs[orbit[full ^ mask]] - costs[mask] for mask in reps]
    with args.output.open("w", newline="", encoding="utf-8") as out:
        writer = csv.writer(out, delimiter="\t", lineterminator="\n")
        writer.writerow(["rep", "complement_rep", "min_size", "excluded_through"])
        writer.writerows((mask, orbit[full ^ mask], costs[mask], costs[mask] - 1) for mask in reps)
    print(f"side {n}, {len(orbit)} masks, {len(reps)} orbits, maximum increase {max(gaps)}")


if __name__ == "__main__":
    main()
