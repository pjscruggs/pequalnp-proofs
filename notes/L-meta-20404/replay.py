from functools import cache
from itertools import combinations

# Bipartite mask 310 in 3 x 4, restricted to the first three columns.
rows = (0b110, 0b011, 0b001)
target = sum(mask << (3 * r) for r, mask in enumerate(rows))
inputs = tuple(
    sum(1 << (3 * r + c) for r in range(3) for c in range(3) if wire in (r, 3 + c))
    for wire in range(6)
)

@cache
def possible(frontier, reuse):
    if len(frontier) == 1 and frontier[0] == target:
        return True
    for i, j in combinations(range(len(frontier)), 2):
        a, b = frontier[i], frontier[j]
        rest = tuple(w for q, w in enumerate(frontier) if q not in (i, j))
        for result in set((a & b, a | b)):
            nxt = rest + (result,)
            if possible(tuple(sorted(nxt)), reuse):
                return True
            if reuse and any(possible(tuple(sorted(nxt + (w,))), False) for w in (a, b)):
                return True
    return False

assert not possible(tuple(sorted(inputs)), True)
print('No <=6-gate circuit on the 3 x 3 restriction:', possible.cache_info())

a,b,c,d,e,f=inputs
gates=(e|f,a&(e|f),d|e,b&(d|e),c&d,(a&(e|f))|(b&(d|e)),((a&(e|f))|(b&(d|e)))|(c&d))
assert gates[-1]==target
print('7-gate witness verified; it also vanishes when all three column indicators are false.')
