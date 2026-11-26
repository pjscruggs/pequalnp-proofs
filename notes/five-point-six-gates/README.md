# Exact six-gate search on five-point two-lit tables

The desk unit L-meta-23799 asks for six AND/OR/NOT gates on the five-point table with mask 283359. Its computational optimum is seven. The exhaustive enumeration excludes six, and Lean 4.36.0 checks the desk's existing seven-gate witness for all 25 ordered pairs. L-meta-21598 previously supplied an eight-gate witness for the same mask. [Prior checked witness](https://github.com/open-goat/pequalnp-proofs/blob/2d3d830051836f24e69ef54e1ec9204201750104/lean/PEqualNP/Outside/L_meta_21598.lean)

## Replay

```sh
c++ -O3 -std=c++17 atlas.cpp -o atlas
./atlas > atlas.txt
```

The output is the compressed table integer and the minimum gate count for every nonconstant table achievable with at most six gates. It includes the five projections at cost zero. In lexicographic order of the 15 pairs `(i,j)` with `0 ≤ i ≤ j < 5`, bit k is the output on pair k. The desk uses the uncompressed index `5*i+j`. Diagonal pairs are singleton inputs. For sizes zero through six, the counts are 5, 25, 130, 395, 930, 2,325, and 4,785. The program asserts that mask 283359 is absent after compression. In the catalog snapshot read at 20:18:50.029 UTC on November 26, 33 five-point units were offerable or held, had no open PR, and asked for a cap of at most six. All 33 nonconstant targets exceeded their caps in this replay. [Snapshot targets](targets.tsv)

For the upper bound, build `PEqualNP.Defs` in the repository's Lean environment and run `lake env lean ../notes/five-point-six-gates/Upper23799.lean` from `lean/`. The exhaustive lower bound is a C++ computation with the completeness argument below. Run `python exact23799.py` for an independent frontier replay of the single desk instance.

## Why the enumeration is exhaustive

Work only on the 15 promised inputs. A circuit prefix is represented by the truth tables of its live wires on those inputs. Enumerate each NOT and both binary operations on every unordered pair of distinct earlier wires. Unary AND and OR are identities, and equal binary operands can be collapsed. Any constant intermediate can be folded into every downstream gate using Boolean identities, so a circuit with nonconstant output needs no constant gates. This also handles the Lean evaluator's out-of-range reads, which default to false. If a newly computed table duplicates an earlier wire, redirect all its uses to the earlier wire. Removing these redundant steps cannot increase size. The search includes every resulting topological order and charges one gate per step.

A separate search with a shrinking frontier must allow a unary NOT when only one wire remains. An early return on frontier size less than two misses the NOR of indicators 0 and 1 at cap two. This table has compressed mask 32256. The two gates are OR(0,1), followed by NOT of its output. Our prefix enumeration includes this case as well as circuits with sharing.

Jukna's graph representation model uses pairs of distinct active vertices. The desk additionally checks repeated points as singleton inputs. Haaswijk et al. give a SAT formulation of exact synthesis by gate selectors, which we used independently on the single six-gate target. [Jukna, *On Graph Complexity*](https://eccc.weizmann.ac.il/report/2004/005/) · [Haaswijk et al., *SAT-Based Exact Synthesis*](https://si2.epfl.ch/demichel/publications/archive/2020/winston-exact.pdf)
