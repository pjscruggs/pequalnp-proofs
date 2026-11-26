# L-meta-20270 needs 25 gates in the four-product construction

The desk asks for a fan-in-two monotone circuit with at most 24 gates for the 8 × 8 table with mask `7093347072485314830`. On each input exactly one row indicator and one column indicator are true. Bit `8*r+c` gives the output at row `r` and column `c`.

Consider circuits that form unions of raw input indicators, take at most four pairwise intersections of those unions, and return the union of the resulting products. The unions that feed the intersections may share any intermediate OR gates. **The exact minimum in this class is 25 gates.** A search for 24 gates must therefore also consider other structures, such as feeding an intersection into a later intersection after an intervening union. The unrestricted 24-gate question remains open in this calculation.

## Prior witness

The upstream proof for L-meta-20042 states a bound of 27 for the same table. Its exhibited list has 25 gates, of which 18 form the input unions, four intersect pairs of them, and three combine the results. Its row masks in order are `0e 51 0b 8c 94 a1 70 62`. [Upstream gate list](https://github.com/open-goat/pequalnp-proofs/blob/95fd09147af03601843592733e5abcc0c3ba71e6/lean/PEqualNP/Outside/L_meta_20042.lean)

Stasys Jukna studies graph representation by circuits on inputs with exactly two active vertices. The desk restricts those pairs to opposite shores. A related project example shows how feeding a computed intersection to two later gates can save an intersection when unions are free. Here each binary union also costs one gate. [Jukna, *On Graph Complexity*](https://eccc.weizmann.ac.il/report/2004/005/) · [Three-intersection sharing example](https://github.com/open-goat/pequalnp-proofs/discussions/23239)

## Exhausting the products

Write one product as `(R₁ ∪ C₁) ∩ (R₂ ∪ C₂)`, where each R contains row indicators and each C contains column indicators. If the two row supports overlap, the product accepts an entire row. Likewise, overlapping column supports accept an entire column. This table has neither a full row nor a full column. Every nonempty product contained in it therefore accepts the two rectangles `R₁ × C₂` and `R₂ × C₁`, either of which may be empty. When both are nonempty, their row sets are disjoint and their column sets are disjoint.

Enumerating nonempty subsets of rows and their common columns gives 93 all-one rectangles. Each rectangle, and each unordered pair disjoint on both shores, gives 2,812 candidate products in total. Starting from an uncovered cell, branch on every product containing it, stopping at depth four. Deduplicating unordered covers gives 128 covers, each using exactly four products. All four products have two nonempty rectangles in every cover. This last check matters because a single rectangle could admit extra unused indicators in a factor. For a pair of nonempty rectangles its two connected components determine both factor supports up to exchanging the factors.

## Charging shared OR gates

For each cover, take its eight factor supports as the required outputs of an OR circuit. A wire feeding two distinct outputs has support contained in their intersection. Enumerate every subset of the optional shared supports of size at least two, treating required outputs as available for sharing as well. Raw indicators are free.

For each selected support S, find the minimum number q of proper selected subsets and raw singletons whose union equals S. These q signals can be joined with q − 1 binary gates. Summing over selected supports gives a realizable cost by building in order of increasing support size. To see that the minimum is exact, take an optimal OR circuit, merge duplicate supports, and select every signal shared by two required outputs. Cut the circuit at required outputs and selected signals. Each remaining private subcircuit has one destination. Connecting its distinct boundary inputs to that destination takes at least their number minus one binary gates. The enumeration considers those inputs, so it attains this lower bound for some selection.

Adding the four product gates and the three output gates gives the following distribution.

| Minimum gates for a cover | Number of covers |
| ---: | ---: |
| 25 | 18 |
| 26 | 34 |
| 27 | 32 |
| 28 | 28 |
| 29 | 14 |
| 30 | 2 |

## Replay

Run `python replay.py` with Python 3.10 or later in this directory. The script uses only the standard library and checks the histogram above. It also evaluates the factor supports directly on the 64 promised inputs. The lower bound for the stated class is an exhaustive Python calculation.

To check the 25-gate upper bound separately, use the project's Lean environment. From its `lean/` directory, run `lake build PEqualNP.Outside.L_meta_20042` and then `lake env lean ../notes/L-meta-20270/Upper.lean`. The theorem `FourProductBound.upper` reuses the exact upstream circuit. Its kernel replay reports only `propext` and `Quot.sound` as axioms. [Lean statement](Upper.lean)
