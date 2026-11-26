# Joint omission penalties for a weighted path and edge

Row and column omissions interact in signed one-a-side circuits. For the core below, omitting row 0 alone or column 1 alone leaves the signed size at seven. Omitting both raises it to nine. The reverse effect occurs for the disjoint edge. Omitting either of its endpoints alone raises the size from seven to nine, and omitting both still costs nine.

```text
1 0 0
0 1 0
1 1 0
0 0 1
```

Rows and columns are numbered from zero. The first three rows and first two columns form a five-vertex path. Row 3 and column 2 are the endpoints of the separate edge. The inputs have one active row and one active column. At most one neighborhood type on each shore can be encoded by an all-zero shore input.

| Omitted row \ omitted column | none | 0 | 1 | 2 |
| --- | ---: | ---: | ---: | ---: |
| none | 7 | 7 | 7 | 9 |
| 0 | 7 | 7 | 9 | 9 |
| 1 | 7 | 9 | 7 | 9 |
| 2 | 8 | 8 | 8 | 9 |
| 3 | 9 | 9 | 9 | 9 |

Every displayed entry is the signed minimum on the 12 promised inputs. The monotone minimum is seven, and neither shore has a type that can be omitted in that basis. Each type has an opposing neighbor missing from another neighborhood on its shore. An exhaustive C++ live-wire search found all 21 core witnesses and ruled out the preceding budget in each case. An independent Python replay verified all 21 core witnesses and exhausted each preceding budget as well. [Haaswijk, exact synthesis on care sets](https://si2.epfl.ch/~demichel/graduates/theses/winston.pdf) · [Jukna, graph representation on weight-two inputs](https://eccc.weizmann.ac.il/report/2004/005/)

## Weighted counts

Give each type a positive multiplicity. The exact signed count is the minimum over omission pairs of the corresponding core entry plus one gate for each extra copy of each retained type. The upper bound ORs retained copies together. For the lower bound, a type with an unread copy can be represented by its all-zero input. Otherwise pinning a live duplicate to false removes its first live gate and leaves the table on the other copies and representatives. Repeat until each retained type has one copy. The monotone count is the total number of physical indicators. [Earlier proof of the weighted lift](https://github.com/pjscruggs/pequalnp-proofs/tree/fa1357e71f9fc53fdfbcc1866cdde768ddb23138/notes/weighted-staircase) · [Checked monotone twin reduction](https://github.com/open-goat/pequalnp-proofs/pull/36865)

An estimate obtained by adding the two costs of omitting a single type can err in either direction. The five-by-five Table 1a mask 31328289 (L-meta-21263) has exact counts **ten monotone and eight signed**. Adding single-omission penalties would predict seven signed gates. For mask 30280769 (L-meta-21249), the exact counts are **ten monotone and nine signed**, while the same estimate predicts ten signed gates. Keeping row type 0 and omitting column type 1 gives eight gates in the first example. Omitting both gives nine. In the second, omitting the two disjoint-edge types together avoids charging the same penalty twice. Direct exhaustive searches on the original 25 cells agreed with the signed profile on all seven examples. The signed upper witnesses replay in Lean 4.36.0. [Prior exact monotone result for L-meta-21263](https://github.com/open-goat/pequalnp-proofs/discussions/13344#discussioncomment-19930369) · [Earlier profiles with additive penalties](https://github.com/pjscruggs/pequalnp-proofs/tree/d74b5b558ac5fe7bd10d7478d36f214f076f4867/notes/weighted-one-a-side-cores)

## Replay

```sh
python3 verify.py
python3 verify.py --critical-exclusions
# The full exhaustive replay takes longer.
python3 verify.py --all-exclusions
# From the project's lean/ directory after building PEqualNP.Defs
lake env lean ../notes/joint-omission-penalties/JointOmissionWitnesses.lean
```

In `profile.tsv`, `-1` means no omission. Wire numbers list the retained row inputs first and the retained column inputs second. Gate outputs follow in gate-list order. In `examples.tsv`, rows are inputs 0–4 and columns are 5–9. The last wire is the output in both tables. The normalized search folds constants and duplicate wire values on the promise. It retains both possible last-use choices for NOT and all last-use choices for AND and OR.
