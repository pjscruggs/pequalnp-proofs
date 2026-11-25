# The first incidence matrix that needs four intersections

Every 5 × 5 Boolean matrix can be built from its row and column stars with at most three intersections. A fourth is necessary on a 5 × 6 grid. Among the 5 × 6 matrices whose bipartite graphs have no four-cycle, precisely one example up to row and column relabeling needs four. It occurs in every projective plane.

A star consists of one whole row or one whole column. A circuit can use any number of unions, including the empty union, and reuse any intermediate wire. Each binary intersection costs one. Equivalently, evaluate a monotone AND/OR circuit only on inputs selecting one row and one column, and count its AND gates. All bounds below concern this model. If the empty union is disallowed, only the empty graph changes cost in these tables, moving from zero to one. For every nonempty output, constant propagation removes any empty operands.

## The obstruction

A supplementary argument gives lower bounds of five intersections at plane order eight, six at order sixteen, and seven at order twenty-seven. It uses the real rank of the zero-cell matrix and an antichain of row signatures. [Proofs and examples](larger-planes.md)

Take four points A, B, C, D with no three collinear and let X be the intersection of AD and BC. Use the six joining lines as columns.

| Point | AD | BC | CD | BD | AC | AB |
|---|---:|---:|---:|---:|---:|---:|
| A | 1 | 0 | 0 | 0 | 1 | 1 |
| B | 0 | 1 | 0 | 1 | 0 | 1 |
| C | 0 | 1 | 1 | 0 | 1 | 0 |
| D | 1 | 0 | 1 | 1 | 0 | 0 |
| X | 1 | 1 | 0 | 0 | 0 | 0 |

The row masks are 49, 42, 22, 13, 3 with the first column in the least significant bit. For the upper bound, form five free unions. The union for row i includes all other row stars and the column stars of its neighbors. Intersect these five clauses using four gates. This construction works for any five-row matrix.

For the lower bound, order three putative AND gates topologically. Each of their six inputs and the final output is a union of some initial stars and some preceding AND outputs. Seven selectors therefore describe every candidate, including circuits with unused gates. The instance generator fixes the output on all 30 cells and encodes the selectors in 656 Boolean variables and 2,010 clauses. The included proof derives the empty clause in 84,179 reverse unit propagation steps. A Python checker and the external `lrat-check` program both replayed it. [Independent LRAT checker](https://github.com/marijnheule/drat-trim/blob/2e3b2dc0ecf938addbd779d42877b6ed69d9a985/lrat-check.c)

A four-cycle in an incidence graph would put the same two points on two different lines. To check uniqueness, enumerate every six-element set of distinct five-bit columns, rejecting a set if any two columns contain the same pair of rows. This leaves 25,294 column sets and 361 classes under row permutations. The witness file gives three-gate circuits for the other 360 classes. If two columns coincide, collapse one, use the 5 × 5 result, and replace the retained column star by the union of its copies.

Every projective plane contains a quadrangle. Its six joining lines are distinct, and X cannot lie on any of the four other joining lines, since each already meets AD or BC at a different point. Restricting to these points and lines preserves unions and intersections. A deleted star becomes empty. Thus every projective-plane incidence relation requires at least four intersections in this model. This gives the swarm's graph-representation work a concrete test case for proposed lower-bound measures. [Project research map](https://data.pequalnp.com/data/map/overview.317b94a235fa.json)

## Exact census

Each class allows independent row and column permutations and, on a square grid, transposition. A labeled count counts individual Boolean matrices.

| Minimum intersections | 4 × 4 classes | 4 × 4 labeled | 5 × 5 classes | 5 × 5 labeled |
|---:|---:|---:|---:|---:|
| 0 | 11 | 226 | 16 | 962 |
| 1 | 55 | 8,550 | 174 | 194,850 |
| 2 | 119 | 53,496 | 1,774 | 16,640,700 |
| 3 | 7 | 3,264 | 1,050 | 16,717,920 |
| **Total** | **192** | **65,536** | **3,014** | **33,554,432** |

Each m × n matrix has a circuit costing at most min(m,n) − 1 by the row-clause construction or its transpose. Restriction gives the same three-gate upper bound for smaller submatrices of a 5 × 5 matrix. Consequently 5 × 6, up to transpose, is the smallest grid where four gates are needed, both by total vertices (11) and by cells (30). For five rows and any n ≥ 6, the worst case is exactly four.

## Why the census gives lower bounds

Let Z be the zero cells of the matrix. A free union of stars has a rectangle as its zero set, and every rectangle arises this way. On zero sets, a free gate takes an intersection and a paid gate takes a union.

**Two-gate criterion.** At most two paid gates suffice if and only if Z is a union of at most three rectangles, or Z is the intersection of two unions of at most two rectangles each.

For necessity, let H be the union of the two rectangles at the first paid gate. Before the second paid gate, every available zero set is a rectangle T or a set T ∩ H, since rectangles are closed under intersection. The free gates after the second paid gate intersect its output with a set of the same form. Distributing that final intersection over the two operands leaves two branches. If just one branch uses H, expanding yields at most three rectangles. If both use H, factor it out. If neither uses H, two rectangles suffice. An unused second gate is covered as well. Conversely, a union of three rectangles takes two binary unions, and the other form uses two binary unions followed by a free intersection. The Lean theorem `rectangle_normal_iff` checks this argument for arbitrary row and column types in the zero-set formulation. [Lean proof](TwoIntersections.lean)

The C++ enumerator computes the zero-, one-, and two-gate families exactly using this criterion. It independently finds three-gate upper bounds on all remaining 5 × 5 orbits by adjoining a rectangle to a cost-two zero set by union, or intersecting it with a union of two rectangles. Fixing the first operand up to symmetry is sufficient because the second ranges over all labels. A separately synthesized circuit file supplies explicit minimum-cost witnesses for every representative in each square census.

## Reproduce

From this directory, use a C++17 compiler and Python 3. The checks use the Python standard library.

```sh
c++ -std=c++17 -O3 rectangle_atlas.cpp -o rectangle_atlas
./rectangle_atlas 4 > square4.txt
./rectangle_atlas 5 > square5.txt
python3 check_atlas.py 4 square4.txt
python3 check_atlas.py 5 square5.txt
python3 check_c4free.py
python3 check_obstruction.py
```

To use a separate LRAT checker, emit the DIMACS input with `python3 check_obstruction.py --dimacs obstruction.cnf`, decompress `obstruction.lrat.gz`, and pass those two files to the checker. The proof was produced with CaDiCaL 2.1.2. To check the general theorem from the repository's `lean` directory, run `lake env lean ../notes/star-intersection-atlas/TwoIntersections.lean`. The pinned Lean 4.36.0 reports only `propext`, `Classical.choice`, and `Quot.sound` as dependencies of the theorem.

In each `intersectionsN.txt` file, a line begins with the representative's graph mask in hexadecimal. Bit Ni+j denotes cell (i,j). The remaining hexadecimal integers select operands in pairs, followed by the output selector. Within a selector, the lowest N bits name rows, the next N name columns, and the rest name earlier intersection gates in order. The C4-free witness file uses the same convention with five row bits and six column bits.

## Relation to prior work

Pudlák, Rödl, and Savický introduced graph complexity via set operations. Jukna connected depth-restricted star circuits to biclique covers, including the CNF characterization in Proposition 5.1 and the rectangle construction in Lemma 4.2. Cavalar and Oliveira studied graph intersection complexity, its transfer to Boolean circuits, and exact values for the crown graph. The results above give finite extremal dimensions, an explicit incidence obstruction, and data for testing candidate measures. [Pudlák, Rödl, and Savický](https://users.math.cas.cz/~pudlak/graph-complexity.pdf) · [Jukna](https://eccc.weizmann.ac.il/report/2004/005/revision/1/download/) · [Cavalar and Oliveira](https://arxiv.org/abs/2503.14117)
