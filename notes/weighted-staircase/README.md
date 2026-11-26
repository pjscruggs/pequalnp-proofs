# Exact counts for weighted staircase tables

The one-a-side table with mask 15762464 (L-meta-20764) needs **eight AND/OR gates and four AND/OR/NOT gates**. The five-by-five example has a four-gate circuit `NOT(row0 OR col4) AND (row4 OR col0)`. Lean 4.36.0 replays that witness on all 25 promised inputs and separately [excludes seven monotone gates](Exact20764.lean). The four-gate witness improves the seven-gate signed control from the earlier Table 1a screen. [Posted monotone statement](https://pequalnp-desk.pequalnp.workers.dev/desk/row?gap=L-meta-20764) · [Earlier signed controls](https://github.com/open-goat/pequalnp-proofs/discussions/30718#discussioncomment-19933288)

## The three-by-three core

Merge identical rows and columns. In this family the resulting matrix, in order of increasing neighborhood size on each shore, is

```text
0 0 0
0 0 1
0 1 1
```

There are three types on each shore. Choose at most one type per shore whose indicators are all omitted. The value on that type must be correct when no visible indicator on its shore is lit. The signed gate count for the three-by-three core is as follows. Here `none` retains all three types on that shore.

| Omitted row \ omitted column | none | 0 | 1 | 2 |
| --- | ---: | ---: | ---: | ---: |
| none | 4 | 4 | 4 | 4 |
| 0 | 4 | 4 | 4 | 5 |
| 1 | 4 | 4 | 4 | 5 |
| 2 | 4 | 5 | 5 | 4 |

In the monotone basis, only the empty type 0 can be omitted. Its all-zero vector is below every visible vector on the same shore. The four feasible monotone entries each cost four. The Python live-wire search and the independent C++ prefix enumeration agree on all 20 core entries. Both evaluate only the nine promised inputs. In the prefix enumeration, equal or constant wire values on these inputs can be folded away by Boolean identities. The search tries NOT of every earlier signal and AND/OR of every distinct pair, with sharing and every earlier signal eligible as output. [Haaswijk, exact synthesis over care sets, §2.6](https://si2.epfl.ch/~demichel/graduates/theses/winston.pdf)

## Lift from the core

For a chosen pair of omitted types, add `multiplicity − 1` for every retained type on either shore. Take the minimum of these sums plus the corresponding core cost. This gives the exact gate count for every choice of positive multiplicities in either basis. The monotone count simplifies to the number of nonisolated vertices.

For the upper bound, OR the copies of each retained type and feed the resulting wire to the core circuit. For the lower bound, prune the output cone and propagate constants. If a type has an unread copy, it can be omitted entirely by representing that type with the unread copy before removal. The remaining instances of that type are zero on those inputs. Two omitted types on one shore would have identical outputs against every opposite type, so there is room for at most one omitted type per shore. Otherwise all copies of a repeated type are live. Make one copy permanently false and remove its first live gate, which becomes a projection or constant. The restricted circuit computes the smaller table. The smaller table still includes each row and column type and remains nonconstant. Induction charges one gate for each copy beyond the representative of every type that is ultimately retained. At the representative table the chosen omitted types are among the cases above. This applies to the one-a-side care set, where two lit vertices on the same shore are outside the promise. [Monotone twin reduction](https://github.com/open-goat/pequalnp-proofs/pull/36865) · [Jukna, graph representation on weight-two inputs](https://eccc.weizmann.ac.il/report/2004/005/)

The listed 13 masks match this three-by-three core. Independently, a search over the original 25 inputs found a signed witness at each predicted size and exhausted the preceding budget. The bundle records all 13 gate lists and their Lean-checked upper bounds. In particular the signed sizes of L-meta-20770 and L-meta-20771 are five, against eight monotone gates in both cases. The profile and induction supply mathematical lower bounds for these signed optima. The Lean file checks the signed witnesses. [Read-once lower bounds for one-a-side tables](https://github.com/open-goat/pequalnp-proofs/discussions/36974)

## Replay

```sh
python3 verify.py
python3 staircase_core.py
c++ -O3 -std=c++17 -Wall -Wextra -Werror staircase-prefix.cpp -o staircase-prefix
./staircase-prefix
# From the Lean project directory after building PEqualNP.Defs
lake env lean ../notes/weighted-staircase/StaircaseWitnesses.lean
```

The monotone Lean check is `lake env lean ../notes/weighted-staircase/Exact20764.lean` from `lean/`. It specializes the previously checked live-wire argument. [Original search](https://github.com/open-goat/pequalnp-proofs/pull/12547) · [Earlier specialization](https://github.com/open-goat/pequalnp-proofs/pull/27751)
