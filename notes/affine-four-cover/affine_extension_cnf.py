"""Generate DIMACS for extensions of the eleven AG(2,4) rectangles to PG(2,4).

python affine_extension_cnf.py DIRECTORY --relax 2
python affine_extension_cnf.py DIRECTORY --relax 3
Each generated formula asks for a 14-cover with the specified affine row
memberships retained on the first sixteen points. All rectangle columns,
infinity memberships, and the remaining rectangles are free.
"""
import argparse
from itertools import combinations, permutations
from pathlib import Path


AFFINE = (69905,74274,83012,100488,164897,149522,139652,135752,
          272449,267394,295444,278824,541313,557378,530468,533528)
ROWS = AFFINE + tuple((15 << (4*d)) | (1 << 20) for d in range(5))
SHAPES = (224,922,3221,4353,9224,12374,18434,22064,33284,43312,49241)
LINES = tuple(frozenset(i for i,row in enumerate(ROWS) if (row >> j) & 1)
              for j in range(21))
SWARM_ROWS = (1179809,262467,524934,1049868,2585,5170,10340,20680,41360,
              82720,165440,330880,661760,1323520,549889,1099778,102405,
              204810,409620,819240,1638480)
POINT_LABEL = (0,1,4,14,2,3,18,6,11,9,20,17,7,12,5,13,8,15,10,19,16)
LINE_LABEL = (7,8,4,13,20,1,11,14,17,6,9,10,5,18,3,19,0,2,16,12,15)


def members(bits):
    return frozenset(i for i in range(16) if (bits >> i) & 1)


def automorphisms():
    arcs = [j for j,m in enumerate(SHAPES) if m.bit_count() == 6]
    rays = [j for j,m in enumerate(SHAPES) if m.bit_count() == 3]
    center, = set.intersection(*(set(members(SHAPES[j])) for j in arcs))
    edge = {i:frozenset(j for j in arcs if i in members(SHAPES[j]))
            for i in range(16) if i != center}
    point = {e:i for i,e in edge.items()}
    assert len(point) == 15 and all(len(e) == 2 for e in point)
    matching = {frozenset(edge[i] for i in members(SHAPES[j])):j for j in rays}
    infinity = {}
    for j in rays:
        central = members(SHAPES[j]) | {center}
        line, = (L for L in LINES if central <= L)
        infinity[j], = line - central
    for perm in permutations(arcs):
        action = dict(zip(arcs,perm))
        def move(e):
            return frozenset(action[v] for v in e)
        images = {j:frozenset(move(e) for e in M) for M,j in matching.items()}
        if set(images.values()) != set(matching):
            continue
        action.update({j:matching[M] for j,M in images.items()})
        on_points = {center:center} | {i:point[move(e)] for i,e in edge.items()}
        on_points.update({v:infinity[action[j]] for j,v in infinity.items()})
        assert {frozenset(on_points[p] for p in L) for L in LINES} == set(LINES)
        for j,s in enumerate(SHAPES):
            assert {on_points[p] for p in members(s)} == members(SHAPES[action[j]])
        yield action


def orbits(count):
    assert set(POINT_LABEL) == set(LINE_LABEL) == set(range(21))
    for i,row in enumerate(ROWS):
        assert sum(1 << LINE_LABEL[j] for j in range(21) if row >> j & 1) == SWARM_ROWS[POINT_LABEL[i]]
    # Independently check coverage by the affine row sets with every legal column.
    for i in range(16):
        for j in range(20):
            assert any(i in members(s) and not members(s) & LINES[j] for s in SHAPES) == (i not in LINES[j])
    group = list(automorphisms())
    assert len(group) == 120
    unseen = set(combinations(range(11),count))
    while unseen:
        first = min(unseen)
        orbit = {tuple(sorted(p[j] for j in first)) for p in group}
        assert orbit <= unseen
        unseen -= orbit
        yield first,len(orbit)


class Formula:
    def __init__(self):
        self.n = 0
        self.clauses = []

    def bit(self):
        self.n += 1
        return self.n

    def add(self, *clause):
        self.clauses.append(clause)

    def write(self,path):
        with path.open("w",encoding="ascii",newline="\n") as f:
            print(f"p cnf {self.n} {len(self.clauses)}",file=f)
            for clause in self.clauses:
                print(*clause,0,file=f)


def encode(relax,budget):
    f = Formula()
    # A true/false constant for a fixed row, otherwise a positive DIMACS id.
    fixed = [shape for j,shape in enumerate(SHAPES) if j not in relax]
    selectors = [[bool(shape >> i & 1) for i in range(16)] + [f.bit() for _ in range(5)]
                 for shape in fixed]
    free = [[f.bit() for _ in range(21)] for _ in range(budget-len(fixed))]
    selectors.extend(free)
    cover = {(i,j):[] for j,L in enumerate(LINES) for i in range(21) if i not in L}
    for xx in selectors:
        for j,L in enumerate(LINES):
            if any(xx[i] is True for i in L):
                continue
            # With rows chosen, take every column avoiding the chosen rows.
            col = f.bit()
            possible = [xx[i] for i in sorted(L) if type(xx[i]) is int]
            f.add(col,*possible)
            for x in possible:
                f.add(-col,-x)
            for i,x in enumerate(xx):
                if i in L or x is False:
                    continue
                if x is True:
                    cover[i,j].append(col)
                else:
                    term = f.bit()
                    f.add(-term,x)
                    f.add(-term,col)
                    cover[i,j].append(term)
    for witnesses in cover.values():
        f.add(*witnesses)
    # Entirely free rectangles can be lexicographically sorted by their rows.
    for a,b in zip(free,free[1:]):
        previous = []
        for i in (*range(16,21),*range(16)):
            x,y = a[i],b[i]
            f.add(*previous,-x,y)
            equal = f.bit()
            f.add(*previous,-x,-y,equal)
            f.add(*previous,x,y,equal)
            previous = [-equal]
    return f


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory",type=Path)
    parser.add_argument("--relax",type=int,choices=range(5),default=2)
    parser.add_argument("--budget",type=int,choices=(14,15),default=14)
    args = parser.parse_args()
    args.directory.mkdir(parents=True,exist_ok=True)
    for representative,size in orbits(args.relax):
        path = args.directory / (f"pg4-k{args.budget}-r" +
                                 "_".join(map(str,representative)) + ".cnf")
        formula = encode(representative,args.budget)
        formula.write(path)
        print(f"{representative}  orbit={size}  vars={formula.n}  "
              f"clauses={len(formula.clauses)}  {path.name}")
