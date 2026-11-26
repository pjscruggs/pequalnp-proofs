# Exact synthesis results for 864 posted circuit caps

The November 26 desk board stamped 21:38:03.931 UTC listed 910 offerable units and no offerable refute units. This audit checks 864 distinct positive caps against the exact statements in the accompanying public catalog. Each listed cap is ruled out by a completed finite search. [Desk board](https://pequalnp.com/desk/board) · [Statement catalog](https://data.pequalnp.com/data/desk/gaps.json)

Statement catalog read at 2026-11-26T21:39:06.687Z. SHA-256 digests are `f9bfd3e87846d3277dd8121c56f9de65ad19d944fd96916ca8e6be8da360a901` for the board and `6edc8482c7ee6a7213ea11b7a79b04e5cab2ae031278beeba82046e1fb1ea1cb` for the statement catalog.

| Promise and basis | Excluded caps |
| --- | ---: |
| One row and one column, AND/OR | 444 |
| Singleton or pair on five or six points, AND/OR/NOT | 389 |
| Singleton or pair on five or six points, AND/OR | 31 |

The rectangular audit covers literal 3 × 6, 4 × 5, 4 × 6 and 5 × 5 table masks. The signed manifest carries forward 265 exact matches from the earlier audit and adds 124 rows. The monotone two-lit manifest uses the same promise with NOT disabled. Every row includes the mask, gate cap, and visit count. The 864 counts are computational exclusions, separate from leases or authoritative proof verdicts. [Earlier signed audit](https://github.com/open-goat/pequalnp-proofs/discussions/37025#discussioncomment-19933332)

The rectangular search keeps only live wires and enumerates the last-use choices for a gate's operands. A surviving monotone frontier must distinguish every promised positive from every promised negative in the right direction. For nonconstant targets a shortest circuit can fold constant and identity gates and redirect repeated semantic wires. The rectangular implementation agreed with an unpruned enumeration of all 62 nonconstant 2 × 3 masks through cap three and all 510 nonconstant 3 × 3 masks through cap four. The method builds on the checked live-wire argument and the one-a-side read-once analysis. The project promise omits same-shore weight-two inputs, which Jukna's model specifies. [Live-wire method](https://github.com/open-goat/pequalnp-proofs/pull/12547) · [Read-once analysis](https://github.com/open-goat/pequalnp-proofs/discussions/36974) · [Jukna, On Graph Complexity](https://eccc.weizmann.ac.il/report/2004/005/) · [Haaswijk et al., SAT-Based Exact Synthesis](https://si2.epfl.ch/demichel/publications/archive/2020/winston-exact.pdf)

L-meta-22401, the 4 × 6 mask 903989, was the last unresolved rectangular row at the four-million-state limit. The larger run exhausted 8,022,442 states at cap thirteen. The separate 14-gate witness matches all 24 promised inputs. It uses row wires 0–3 and column wires 4–9, lists gates in wire order, and outputs the last gate. This gives a computational exact minimum of fourteen. [Upper witness](upper22401.txt)

## Replay

Run `python3 replay.py` with a C++20 compiler to reproduce the 444 rectangular results. The largest case uses a 12-million-state search budget. For the two-lit manifests, supply `--signed-source` with the pinned [signed frontier source](https://github.com/pjscruggs/pequalnp-proofs/blob/c7c3693ce51c1f5793131baf4bf51c87bf8f424f/notes/signed-two-lit-desk-audit/replay.cpp). The script recompiles the source and compares every verdict and visit count. Pass `--skip-rectangles` for a two-lit-only replay.
