"""Regenerate the 5 x 6 synthesis instance and check its RUP-only LRAT proof."""
import argparse
import gzip
from pathlib import Path

ROWS = (49, 42, 22, 13, 3)


def instance():
    clauses = []
    count = 0

    def fresh():
        nonlocal count
        count += 1
        return count

    def conjunction(a, b):
        result = fresh()
        clauses.extend([[-a, -b, result], [a, -result], [b, -result]])
        return result

    def free_union(gates):
        selectors = [fresh() for _ in range(11 + len(gates))]
        mask = []
        for i in range(5):
            for j in range(6):
                terms = [selectors[i], selectors[5+j]]
                terms.extend(conjunction(selectors[11+k], gate[6*i+j])
                             for k, gate in enumerate(gates))
                result = fresh()
                clauses.append([*terms, -result])
                clauses.extend([[-term, result] for term in terms])
                mask.append(result)
        return mask

    gates = []
    for _ in range(3):
        a, b = free_union(gates), free_union(gates)
        gates.append([conjunction(x, y) for x, y in zip(a, b)])
    output = free_union(gates)
    for i, row in enumerate(ROWS):
        for j in range(6):
            variable = output[6*i+j]
            clauses.append([variable if (row >> j) & 1 else -variable])
    return count, clauses


def rup(clause, hints, known):
    # Assume every literal of the proposed clause false. Each cited clause
    # must then force a literal, or contradict the accumulated assignment.
    values = {abs(lit): lit < 0 for lit in clause}
    if len(values) != len(set(clause)):
        raise ValueError("tautological addition")
    for hint in hints:
        unit = None
        for lit in known[hint]:
            value = values.get(abs(lit))
            if value is None:
                if unit is not None and lit != unit:
                    raise ValueError("non-unit hint")
                unit = lit
            elif value == (lit > 0):
                raise ValueError("satisfied hint")
        if unit is None:
            return
        values[abs(unit)] = unit > 0
    raise ValueError("hints did not produce a contradiction")


def verify(variables, clauses):
    known = dict(enumerate(clauses, start=1))
    last = len(known)
    additions = 0
    with gzip.open(Path(__file__).with_name("obstruction.lrat.gz"), "rt",
                   encoding="ascii") as proof:
        for line in proof:
            fields = line.split()
            if fields[-1] != "0":
                raise ValueError("missing terminator")
            if fields[1] == "d":
                for idx in map(int, fields[2:-1]):
                    del known[idx]
                continue
            idx = int(fields[0])
            if idx <= last:
                raise ValueError("clause IDs must increase")
            last = idx
            cut = fields.index("0", 1)
            clause = list(map(int, fields[1:cut]))
            if any(abs(lit) > variables for lit in clause):
                raise ValueError("variable outside the encoding")
            rup(clause, map(int, fields[cut+1:-1]), known)
            additions += 1
            if not clause:
                print(f"Verified the empty clause after {additions:,} RUP additions")
                return
            known[idx] = clause
    raise ValueError("missing empty clause")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dimacs", type=Path, help="write the input for an external LRAT checker")
    args = parser.parse_args()
    n, clauses = instance()
    if args.dimacs:
        with args.dimacs.open("w", encoding="ascii", newline="\n") as out:
            print("p cnf", n, len(clauses), file=out)
            for clause in clauses:
                print(*clause, 0, file=out)
    else:
        verify(n, clauses)
