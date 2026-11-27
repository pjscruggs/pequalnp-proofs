# Two decoder restrictions for the ten-label crown

In the 3 × 3 grid plus one lone label construction, **any monotone decoder of at most 11 gates must reuse at least two distinct internal gate outputs**. Primary inputs can be used arbitrarily often, and the single shared internal output in the excluded class may have any fan-out. This is an exhaustive native computation. The general 11-gate decoder and the unrestricted 33-gate crown circuit remain open. [Earlier search and 12-gate upper bound](https://github.com/open-goat/pequalnp-proofs/discussions/21642#discussioncomment-19933561)

Each label first merges its left and right pins with an OR. Nine labels occupy a 3 × 3 grid. Form a signal for each of its three rows and three columns, plus the merged input for the lone label. The seven signals cost 22 gates. A decoder must reject the ten singleton labels and accept the 45 distinct unordered pairs. The 12-gate positive control is reconstructed and tested independently on all 100 ordered inputs.

**The same restriction holds for a 10-gate decoder on the 2 × 5 grid.** Its two row and five column signals cost 23 gates including the ten initial merges. Reaching 33 gates in either grid therefore requires at least two distinct internal decoder outputs to feed multiple gate inputs. This gives an additional constraint for a SAT search on the two fixed grids.

## Exhaustion

If only one internal gate output is reused, call it `w`. The gates upstream of `w` form a formula. After replacing that output by a new input, the remaining gates also form a formula. Both formulas may read the seven original signals, and the second may contain any number of occurrences of `w`.

* For a first formula of minimum cost one through five, enumerate its distinct truth tables modulo row permutations, column permutations and grid transposition. The respective orbit counts are 6, 20, 63, 198 and 650. In each case a search over the eight available inputs excludes a second formula within the remaining budget. Plain formulas are checked separately. A constant or an original input can be substituted directly.
* If the first formula needs at least six gates, the second can use at most five. Enumerate its pair of truth tables at `w = 0` and `w = 1`. Monotonicity forces their pointwise order. Reject pairs whose lower table accepts a negative input or whose upper table rejects a positive input. For each surviving pair, require the first formula to supply the positives missed by the lower table and to exclude negatives accepted by the upper table. All 2,301 compatible pairs are excluded within their respective remaining budgets.

For the 2 × 5 grid, first formulas of costs one through four give 5, 12, 33 and 90 orbits under row and column permutations. For a first formula of cost five or more, the second again has at most five gates. All 1,902 compatible pairs are excluded with no cutoffs.

The formula search generates small subformulas by their truth tables. A formula of size `k` has a child of size at most `floor((k - 1) / 2)`. For an OR, such a child must reject every required negative, and the other child must accept the remaining positives. The AND case is dual. A pruning bound uses the fact that each leaf of a monotone formula corresponds to a rectangle in its Karchmer–Wigderson protocol. Pairs with only one distinguishing input force a leaf of that color. If the forced cells for two colors have intersecting rectangular hulls, at least one color must use multiple leaves. [Karchmer and Wigderson](https://doi.org/10.1137/0403021)

## Replay

Run `python replay.py` from this directory with Python 3.10+ and a C++20 compiler. The default compiler is `g++`. Set `CXX` to another compiler executable if needed. The script builds both search programs in a temporary directory, checks the 12-gate control, and fails if any search hits its limit. All computation runs locally on one core.
