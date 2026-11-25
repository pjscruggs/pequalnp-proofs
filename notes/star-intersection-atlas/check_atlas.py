"""Compare witnesses to an independent orbit census and evaluate each circuit."""
import argparse
from collections import Counter
from itertools import zip_longest
from pathlib import Path


def select(selector, wires):
    if selector >= 1 << len(wires) or selector < 0:
        raise ValueError("wire selected before it is available")
    value = 0
    for i, wire in enumerate(wires):
        if (selector >> i) & 1:
            value |= wire
    return value


def evaluate(rows, cols, selectors):
    if len(selectors) % 2 != 1:
        raise ValueError("expected two input selectors per gate and one output selector")
    wires = [((1 << cols) - 1) << (i*cols) for i in range(rows)]
    wires += [sum(1 << (i*cols+j) for i in range(rows)) for j in range(cols)]
    for a, b in zip(selectors[:-1:2], selectors[1:-1:2]):
        wires.append(select(a, wires) & select(b, wires))
    return select(selectors[-1], wires)


def check(n, census_path):
    witnesses = Path(__file__).with_name(f"intersections{n}.txt")
    classes, labels = Counter(), Counter()
    previous = -1
    with census_path.open(encoding="ascii") as census, witnesses.open(encoding="ascii") as certs:
        for row, certificate in zip_longest(census, certs):
            if row is None or certificate is None:
                raise ValueError("orbit lists have different lengths")
            graph_hex, size, upper = row.split()
            graph = int(graph_hex, 16)
            witness_graph, *selectors = (int(s, 16) for s in certificate.split())
            if graph <= previous or graph != witness_graph or int(size) < 1:
                raise ValueError(f"inconsistent orbit at {graph_hex}")
            if int(upper) > 3 or int(upper) != len(selectors) // 2:
                raise ValueError(f"cost mismatch at {graph_hex}")
            if evaluate(n, n, selectors) != graph:
                raise ValueError(f"circuit does not produce {graph_hex}")
            previous = graph
            classes[int(upper)] += 1
            labels[int(upper)] += int(size)
    if sum(labels.values()) != 1 << (n*n):
        raise ValueError("labeled count does not cover the domain")
    print("intersections   classes    labeled")
    for k in sorted(classes):
        print(f"{k:13d} {classes[k]:9d} {labels[k]:10d}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("n", type=int, choices=(4, 5))
    parser.add_argument("census", type=Path)
    args = parser.parse_args()
    check(args.n, args.census)
