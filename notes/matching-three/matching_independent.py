"""Independent Python exact monotone matching cap replay."""
from functools import cache
from itertools import combinations, permutations

minterm = tuple(sum(1 << (3*i+p[i]) for i in range(3)) for p in permutations(range(3)))
def matches(row): return any(row&m==m for m in minterm)
maxfalse = tuple(row for row in range(512) if not matches(row)
                 and not any(row!=other and row&other==row and not matches(other) for other in range(512)))
assert len(maxfalse)==15
rows = minterm + maxfalse
target = (1<<len(minterm))-1
full=(1<<len(rows))-1
pair_count=len(minterm)*len(maxfalse)
pairs=((i,j) for i in range(len(minterm)) for j in range(len(minterm),len(rows)))
comparisons=tuple(pairs)
inputs=tuple(sum(1<<i for i,row in enumerate(rows) if row>>pin&1) for pin in range(9))
for pin in range(9):
    hit=next(r for r in minterm if r>>pin&1)
    miss=hit^(1<<pin)
    assert not matches(miss)
    assert any(miss & n==miss for n in maxfalse)

@cache
def separating_mask(signal):
    return sum(1<<i for i,(a,b) in enumerate(comparisons) if signal>>a&1 and not signal>>b&1)

def exists(wires, budget):
    if len(wires)==1 and wires[0]==target:
        return True
    slack=budget+1-len(wires)
    if not budget or slack<0:
        return False
    separated=0
    for wire in wires:
        separated |= separating_mask(wire)
    if separated != (1<<pair_count)-1:
        return False
    return explore(wires, budget)

@cache
def explore(wires, budget):
    slack=budget+1-len(wires)
    for a,b in combinations(wires,2):
        rest=tuple(w for w in wires if w not in (a,b))
        for new in (a&b,a|b):
            if new in (0,full) or new in wires:
                continue
            for k in range(min(2,slack)+1):
                for uses in combinations((a,b),k):
                    if exists(tuple(sorted((*rest,*uses,new))),budget-1):
                        return True
    return False

present=exists(tuple(sorted(inputs)),13)
print('cap 13', 'PRESENT' if present else 'EXHAUSTED', explore.cache_info(), flush=True)
assert not present
