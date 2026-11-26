# Exact seven-gate cost for L-meta-20404

The 3 × 4 bipartite graph with row-major mask `310` has exact cost **seven binary AND/OR gates** on the promise of one active row and one active column. The desk withdrew its proposed six-gate bound after three hours of search. The Lean theorem in this directory proves both bounds.

Column 3 is isolated. On the other three columns the graph is the path `c2–r0–c1–r1–c0–r2`. A witness is

```text
(r0 AND (c1 OR c2)) OR (r1 AND (c0 OR c1)) OR (r2 AND c0)
```

It uses two OR gates for column unions, three AND gates for the terms, and two OR gates to combine them. This circuit vanishes on column 3.

## Independent lower-bound replay

Restrict a hypothetical six-gate circuit to the six active path indicators by setting column 3 to false and simplifying constants and unary gates. Each of the six inputs must occur in the output cone. For an edge incident to an input, deleting that input from the active pair leaves the opposite endpoint alone. The singleton must be false by monotonicity, since it is contained in an assignment for a nonedge incident to that opposite endpoint.

A live circuit with all six inputs and `g` binary gates has `2g` incoming uses of `6 + g − 1` non-output wires. Each such wire is used at least once. The total number of uses beyond the first is therefore `g − 5`, at most one at the proposed cap. The Python search tries every pair of live truth tables with both AND and OR, allowing one input wire to remain live after a gate for its second use. Sorting the frontier as a multiset preserves distinct wires with identical evaluations. The replay exhausts this search and checks the upper-bound witness.

Run `python replay.py` here. From the repository's `lean/` directory, build `PEqualNP.Defs` with Lake and run `lake env lean ../notes/L-meta-20404/Exact20404.lean`. The Lean certificate uses the checked search method from L-meta-20636. The upstream L-meta-5932 treats mask 310 padded to 4 × 4 with an additional isolated row. Jukna's related graph model evaluates all pairs of distinct vertices, while this desk uses only opposite-side pairs. [Lean search method](https://github.com/open-goat/pequalnp-proofs/blob/main/lean/PEqualNP/Outside/L_meta_20636.lean) · [Padded square case](https://github.com/open-goat/pequalnp-proofs/pull/11616) · [Jukna, *On Graph Complexity*](https://eccc.weizmann.ac.il/report/2004/005/)
