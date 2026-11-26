# Two weighted one-a-side profiles

For the five-by-five graph L-meta-21262 (mask 30475297), the minimum is **ten AND/OR gates and six AND/OR/NOT gates**. Lean 4.36.0 checks the six-gate witness on all 25 promised inputs. The exact signed lower bound follows from the profile below and a separate search on the original table. The monotone count agrees with the previously reported Lean exclusion of nine and the merged ten-gate witness L-meta-20867. [Prior exact monotone result](https://github.com/open-goat/pequalnp-proofs/discussions/35390) · [Merged upper bound](https://github.com/open-goat/pequalnp-proofs/pull/28339)

The two cores below are ordered by row and column type. The first has an empty row and overlapping nonempty rows. The second is a four-vertex path with a disjoint edge. In the second matrix the disjoint edge is at row 1 and column 1, with zero-based numbering.

```text
0 0 0       1 0 0
1 1 0       0 1 0
1 0 1       1 0 1
```

Let `a0,a1,a2` and `b0,b1,b2` be positive multiplicities of the row and column types and let `N` be their sum. Write `r` and `c` for the omitted types, allowing no omission. On an omitted type, the input to that shore is all zero. These are the **exact core costs** before expanding the multiplicities.

| Core | Monotone | Signed |
| --- | --- | --- |
| Overlapping rows | 5, with no omissions or with row 0 omitted | 5 plus 1 if row 1 or row 2 is omitted |
| Path and disjoint edge | 6, with no omissions | 6 plus 1 for omitting row 1 and another 1 for omitting column 1 |

For the monotone basis the omitted type must have a neighborhood contained in all other neighborhoods on that shore, by coordinatewise monotonicity. This leaves the three monotone cases in the table. The signed profile permits every omission pair. Two independent exact searches checked **35 profile entries**. The live-wire search tracks distinguishable promised cells, and the gate-selector SAT cross-check asserts each reported size feasible and its predecessor infeasible. Only the nine one-a-side inputs are specified. [Haaswijk, exact synthesis on care sets, §2.6](https://si2.epfl.ch/~demichel/graduates/theses/winston.pdf) · [Jukna, graph representation on weight-two inputs](https://eccc.weizmann.ac.il/report/2004/005/)

## Exact counts after expansion

Use the [same twin lift and deletion proof as for the staircase profile](https://github.com/pjscruggs/pequalnp-proofs/tree/fa1357e71f9fc53fdfbcc1866cdde768ddb23138/notes/weighted-staircase). For a fixed choice of omitted types, OR the physical copies of each visible type to obtain its representative input. The cost of this lift is the sum of multiplicity minus one over visible types. Conversely, an unread copy lets the type be represented by an all-zero shore input. If every copy of a repeated type is live, fixing one copy to zero removes at least one gate and leaves all representative types present. Repeated restriction gives the same cost lower bound for the finally visible types. [Checked monotone twin reduction](https://github.com/open-goat/pequalnp-proofs/pull/36865) · [Prior monotone read-once obstruction](https://github.com/open-goat/pequalnp-proofs/discussions/36974)

The additive penalties in the signed profiles let the two shores choose omissions independently. Minimizing the lift cost plus the core count gives these formulas for all positive multiplicities.

- Overlapping rows. The monotone size is `N - a0`. The signed size is `N - 1 - max(0,a0-1,a1-2,a2-2) - (max(b0,b1,b2)-1)`.
- Path and disjoint edge. The monotone size is `N`. The signed size is `N - max(0,a0-1,a1-2,a2-1) - max(0,b0-1,b1-2,b2-1)`.

The example table gives 22 desk masks and their predicted costs. An exhaustive signed frontier search on the original 25 cared inputs agreed with all 22 predictions, and Lean checks all 22 explicit signed witnesses. These are research checks. The official Table 1a caps use the monotone basis.

## Replay

Run from this directory.

```sh
python3 verify.py
python3 core_profile.py
# With python-sat and the CaDiCaL 1.9.5 backend available
python3 profile_sat.py
# From the project's lean/ directory after building PEqualNP.Defs
lake env lean ../notes/weighted-one-a-side-cores/CoreWitnesses.lean
```

Each gate in `examples.tsv` lists its operation and operands. Rows are wires 0–4, columns 5–9, and new wires follow in gate-list order. The last wire is the output. In the SAT replay, repeated inputs on AND gates permit identity padding, so a fixed-budget query covers every smaller circuit as well.
