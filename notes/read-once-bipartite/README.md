# Read-once formulas on the one-a-side promise

Let a bipartite graph specify the output when one row indicator and one column indicator are true. Call a row or column full if it contains only ones. For a graph with at least one edge, a monotone read-once formula exists exactly when deleting the full rows and full columns leaves a disjoint union of complete bipartite components and isolated vertices.

## Proof

The singleton assignment for any nonfull vertex must evaluate to zero. It is contained in a promised nonedge, so monotonicity forces its value. Flatten the OR gates at the top of a read-once formula. The resulting branches have disjoint variable sets. Each is either a variable or has an AND at its root.

Each positive pair of nonfull vertices must be accepted by one branch. A branch receiving only one of the active variables would have to accept its singleton, and a branch receiving neither evaluates to zero. Thus the branch contains both endpoints. Connectivity puts every vertex of a nontrivial component in the same branch. Each edge crosses the two children of that branch's top AND because both children must receive an active variable. Connectivity then puts all the component's row vertices on one child and all its column vertices on the other. Each endpoint occurs in some edge, so its child accepts it as a singleton. This forces every cross-pair within the component to be accepted.

Conversely, use each full-line indicator as an OR term. For each remaining nontrivial component, OR its row indicators, OR its column indicators, and AND the two results for a further term. OR all terms. Their supports are disjoint.

## Applying the test to a gate budget

An indicator is essential if it has a positive entry opposite a nonfull vertex. On that positive pair the circuit outputs one, while deleting the indicator leaves a singleton forced to zero. If there are at least `e` essential variables, a live output cone with `g` gates has at least `e+g-1` wire occurrences and at most `2g`. At `g ≤ e-1` these bounds meet. All gates are binary, every non-output wire has one use, and the cone is a read-once formula. A non-biclique component therefore gives the stronger bound `g ≥ e`.

For L-meta-20954, mask 104319 has row masks `31, 27, 5, 3`. Row 0 and column 0 are full. Rows 1 and 3 and columns 1 and 3 give three edges with the corner (3,3) missing. All nine indicators are essential, so eight gates are impossible. A nine-gate witness is the OR of r0, c0, and the three terms `(r1 OR r3) AND c1`, `r1 AND (c3 OR c4)`, and `r2 AND c2`.

[Exact20954.lean](Exact20954.lean) checks the instance's upper and lower bounds using the search engine from L-meta-20636. From the repository's Lean directory, build `PEqualNP.Defs` with Lake, then run `lake env lean ../notes/read-once-bipartite/Exact20954.lean`. The general argument above is a written proof.

## Related work

Jukna studies graph representation on the promise of two active vertices, allowing pairs within either shore. Golumbic, Mintz, and Rotics discuss the induced-path obstruction for total positive Boolean functions. Here the proof uses only opposite-shore pairs and accounts explicitly for full lines. The checked desk proof for the 4 × 4 padded path already supplies a small example where the read-once lower bound separates adjacent gate budgets. [Jukna, *On Graph Complexity*](https://eccc.weizmann.ac.il/report/2004/005/) · [Golumbic, Mintz, and Rotics, *An improvement on the complexity of factoring read-once functions*](https://www.cs.haifa.ac.il/~golumbic/papers/J53-An%20Improvement-GMR2008-DAM.pdf) · [L-meta-20636](https://github.com/open-goat/pequalnp-proofs/blob/main/lean/PEqualNP/Outside/L_meta_20636.lean) · [L-meta-5932](https://github.com/open-goat/pequalnp-proofs/pull/11616)

## Desk snapshot

Run `python scan.py gaps.json` on a saved [public desk catalog](https://data.pequalnp.com/data/desk/gaps.json). On the snapshot read at 20:05:00.452 UTC on November 26, 2026, it flagged **329** offerable monotone mask statements with no PR and with weight above one. The filter considers tables of at most 150 cells. The snapshot SHA-256 is `8805d0aa07a13c17528a4d53003ffbb6b361ebe880a6ba290e4f6a082dd2414f`. The scan applies the written argument to each mask. The accompanying Lean theorem checks L-meta-20954 individually.

For **292** of the 329 tables, the scan also constructs a matching upper bound by splitting the neighborhood of a single nonfull vertex into two nonempty parts. Temporarily treat those parts as neighborhoods of two copies of the vertex. When the resulting components are bicliques, use the converse construction above and identify the two copies with the original indicator. The formula reads that indicator twice. If all other used indicators are essential and every essential indicator occurs, the formula has e + 1 leaves and e gates, matching the obstruction.
