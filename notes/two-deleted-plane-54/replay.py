"""Check the literal graph, matching certificate, gate count and full truth table."""

from itertools import combinations
from pathlib import Path
import re

source = Path(__file__).with_name("Upper54.lean").read_text(encoding="utf-8")
statement = source.split("theorem upper54 :", 1)[1]
edges = {tuple(map(int, pair)) for pair in re.findall(r"x (\d+) && x (\d+)", statement)}
columns = {v: {u for u,w in edges if w == v} for v in range(13,24)}
assert len(edges) == 44 and all(len(points) == 4 for points in columns.values())
assert all(len(a & b) == 1 for a,b in combinations(columns.values(), 2))
representatives = [2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8]
assert len(set(representatives)) == 11
assert all((u,v) in edges for u,v in zip(representatives, range(13,24)))

gate_list = re.search(r"def circuit : Circuit :=\s*⟨\[(.*?)\],\s*(\d+)\s*⟩", source, re.S)
assert gate_list and int(gate_list[2]) == 77
gates = [(op, int(a), int(b)) for op,a,b in
         re.findall(r"⟨\.(and|or), \[(\d+), (\d+)\]⟩", gate_list[1])]
assert len(gates) == 54 and all(max(a,b) < 24+k for k,(_,a,b) in enumerate(gates))
width = 1 << 16
ones = (1 << width) - 1
low = []
for i in range(16):
    half = 1 << i
    block = ((1 << half) - 1) << half
    low.append(block * (ones // ((1 << (2*half)) - 1)))
for high in range(256):
    wires = low + [ones if high & (1 << i) else 0 for i in range(8)]
    target = 0
    for u,v in edges:
        target |= wires[u] & wires[v]
    for op,a,b in gates:
        wires.append(wires[a] & wires[b] if op == "and" else wires[a] | wires[b])
    assert wires[-1] == target
print("54 gates; 2^24 assignments checked; matching size 11; no four-cycle.")
