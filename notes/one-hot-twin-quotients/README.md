# A pendant extension of the seven-vertex path

L-meta-23705 asks for at most ten AND/OR gates on the one-a-side inputs of the 4 × 6 table with mask 839029. Its exact cost is eleven. The same reduction classifies 15 catalog entries beyond the 42 in the earlier seven-vertex path census. [Earlier discussion](https://github.com/open-goat/pequalnp-proofs/discussions/37052)

The row masks are 53, 53, 12 and 3. Merge rows 0 and 1 and columns 4 and 5 to obtain the 3 × 5 mask 3477, whose row masks are 21, 12 and 3. Its column 4 is a leaf adjacent to row 0. Deleting it gives the seven-vertex path `c3–r1–c2–r0–c0–r2–c1`, which has checked cost eight up to relabeling and isolated-row padding. The pendant column is essential before deletion. The promised pair `(r0,c4)` is positive and `(r0,c1)` is negative, so omitting `c4` would make the positive input coordinatewise at most the negative one. Pinning `c4` to zero thus removes at least one live gate. [Checked padded path](https://github.com/open-goat/pequalnp-proofs/blob/e6eee5622d2daa4d9b5e2080d6a687680ec0960b/lean/PEqualNP/Outside/L_meta_6161.lean#L539)

The 3 × 5 table has a nine-gate circuit. Use an OR of three row terms, whose column sets are `{0,2,4}`, `{2,3}` and `{0,1}`. Each term ANDs its row indicator with its column union. Replacing each of the two merged indicators by an OR restores the original table in eleven gates. In the reverse direction the twin deletions also save at least one gate apiece. Every core vertex has a neighbor opposite a nonfull vertex, so its singleton can be compared with both a positive pair and a negative pair. This forces each indicator into the output cone for every intermediate table in the deletion. [Checked twin deletion antecedent](https://github.com/open-goat/pequalnp-proofs/pull/36865)

For any table obtained from mask 3477 by cloning vertices and adding full rows or columns, the same argument gives exact cost `9 + (rows + columns − 8)`. The classifier tests equality of the core up to permutations and transposition after removing full lines and merging equal lines. The [catalog results](targets.tsv) use the [public desk catalog](https://data.pequalnp.com/data/desk/gaps.json) downloaded on November 26, 2026 at 20:37 UTC with SHA-256 `3c5d434081e41881defdbb0e15b6c8b6e61fbf0bfd956dcba9c2855e76db11cad`. All 15 caps are one below the optimum and eight were marked offerable.

The Python replay also verifies the upper bounds on all promised inputs and directly exhausts circuits one gate above the connectivity floor on both small quotients. A trimmed binary DAG with eight essential raw inputs and eight gates has one vertex used twice, since it has sixteen vertices and sixteen edges. The subcircuit ending at that vertex is a read-once formula, and unfolding its two uses yields a second read-once formula on the remaining raw inputs and two copies of the shared truth table. The replay enumerates both formulas, including the case where the shared vertex is a raw input. Seven-gate circuits are read-once, and fewer gates cannot connect eight essential inputs.

```sh
python -B twin_core.py
python -B family_3477.py gaps.json
```

Run these commands in this directory, with `gaps.json` a saved copy of the catalog. Lean 4.36.0 also checked the explicit 11-gate upper bound for mask 839029 locally.

The two quotient checks cover mask 3477 and the 4 × 4 mask 13743 from L-meta-23742. The latter table already has a checked nine-gate optimum upstream. [Checked square quotient](https://github.com/open-goat/pequalnp-proofs/pull/12516) · [Earlier one-wire-use count on the six-vertex path](https://github.com/open-goat/pequalnp-proofs/discussions/36028)
