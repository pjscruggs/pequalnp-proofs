# Exact gate counts for extensions of the seven-vertex path

On the one-a-side promise, start with the bipartite path on seven vertices. Replace each vertex by any positive number of twins, preserving adjacency between groups. Then add any number of full rows or full columns. Full vertices are adjacent to every vertex across the table. If the resulting table has n rows and m columns, its exact monotone fan-in-two gate count is **n+m+1**.

## Base and extensions

The base path has exact size eight. L-meta-6161 checks that value for the 4 × 4 mask 858, which adds one isolated row to the path. A circuit for the path also works on the padded table by ignoring the extra row wire. Each original column is nonfull, so its singleton assignment evaluates to false by monotonicity. Conversely, setting the isolated row indicator to false recovers the path. The orbit with 3 × 4 row masks 12, 5, 3 has an eight-gate witness. Write a = r0 OR c0, b = r1 OR c1, d = r2 OR c2, and e = r1 OR c3. The output is (d AND (a OR b)) OR (e AND a). [Checked padded base](https://github.com/open-goat/pequalnp-proofs/blob/e6eee5622d2daa4d9b5e2080d6a687680ec0960b/lean/PEqualNP/Outside/L_meta_6161.lean#L539)

For the upper bound, OR the indicators within each twin group and feed the result into the corresponding path input. OR each full vertex indicator into the output. These changes add one gate for each vertex beyond the seven in the path.

For the lower bound, every indicator has a positive entry opposite a nonfull vertex. For a path vertex take a core neighbor. For a full vertex take any core vertex on the opposite side. Core vertices stay nonfull because every core group remains nonempty. The singleton of the opposite vertex is forced false by one of its nonedges, while the positive pair is true. Thus every indicator must be read in the output cone.

Now pin any one extra indicator to false. Retaining a representative of every core group preserves the argument for every remaining indicator. The pinned wire has a live gate reading it, since the output cannot be a single raw wire. Its first such gate simplifies to a constant or a copy of another wire. Propagate constants and copies in topological order and renumber the survivors. A false wire can use an out-of-range index in the desk evaluator. Existing true constants can keep their original gates, and setting one input false introduces no new true constant. The circuit therefore loses at least one gate. Repeating until just the path remains gives the claimed lower bound.

The project's twin extension and elimination theorems supply the two local operations. Carmosino, Dang, and Jackman give related one-gate extension and elimination arguments for total Boolean functions. Jukna's graph representation model supplies the context for promised pairs. [Twin extension](https://github.com/open-goat/pequalnp-proofs/blob/e6eee5622d2daa4d9b5e2080d6a687680ec0960b/lean/PEqualNP/Outside/L_meta_19395.lean) · [Twin elimination](https://github.com/open-goat/pequalnp-proofs/pull/36865) · [Carmosino, Dang, and Jackman](https://doi.org/10.4230/LIPIcs.STACS.2026.23) · [Jukna](https://eccc.weizmann.ac.il/report/2004/005/)

## Desk instances

L-meta-23742 has row masks 63, 50, 13, 3. Delete the full row and collapse column pairs (2,3) and (4,5). The result is a seven-vertex path. Its exact cost is therefore 11, one above the posted cap. As a second route, keep the full row and collapse only the column pairs. The quotient is the 4 × 4 mask 13743, whose exact nine-gate cost is already checked. [Checked square quotient](https://github.com/open-goat/pequalnp-proofs/blob/e6eee5622d2daa4d9b5e2080d6a687680ec0960b/lean/PEqualNP/Outside/L_meta_6299.lean#L621)

Run `python scan.py gaps.json` on a saved [public desk catalog](https://data.pequalnp.com/data/desk/gaps.json). The 20:28:14.568 UTC November 26, 2026 snapshot has 42 matching units, 22 of which were marked offerable. All 42 posted caps are one below the exact count. The snapshot SHA-256 is `3b9853647de2fbc50c60c5e7ab969daf86c90481417ee05e07c54c5d15c884b6`. [Captured targets](targets.tsv)

From the repository's Lean directory, build `PEqualNP.Defs` with Lake and run `lake env lean ../notes/path-seven-extensions/Upper23742.lean` to check the 11-gate witness. The lower bound uses the written deletion argument and the checked base. A separate exact search exhausted 3,973 live-frontier states at ten gates.
