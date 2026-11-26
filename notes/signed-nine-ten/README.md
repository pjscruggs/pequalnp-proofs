# Exact signed circuit sizes for 54 six-point tables

The November 26, 2026 desk catalog listed 54 canonical six-point
`FanInTwo` statements between L-meta-25016 and L-meta-25135 with a
posted cap of nine or ten. Exhaustive finite replay and scalar evaluation
give exact size ten for all 44 cap-nine cases and exact size eleven for
all ten cap-ten cases. The domain consists of the 21 singleton or
unordered pair supports. The witness checker evaluates all 36 ordered
pairs against the original upper-triangular mask.

```sh
c++ -std=c++20 -O3 replay.cpp -o replay
python3 verify.py ./replay
```

The replay extends the [earlier signed frontier audit](https://github.com/open-goat/pequalnp-proofs/discussions/37025#discussioncomment-19933332)
to eleven gates. After restricting nodes to the specified support domain,
constants can be propagated and duplicate truth words can be merged.
The search enumerates live input subsets and AND, OR and NOT operations
on live wires with every feasible retention choice. The live wire count
bounds remaining NOT gates because each merge removes at most one live
wire. A positive-negative pair must be separated somewhere in the live
frontier, and must be separated in the forward direction when no NOT
can remain. An exclusion counts only when the search exhausts the
remaining frontiers without hitting the visit limit. The scalar
checker independently replays the gate list at the next depth.

For 13 cases with twins, the checker also verifies the exact sizes of
the smaller quotients. A twin class has identical full target rows,
including diagonals. Merging the inputs within each class by OR maps any
singleton or pair support to the quotient. Conversely, each deleted
input is essential even after earlier deletions, as witnessed by a
retained singleton and the pair obtained by adding that input. Fixing
it to false eliminates its first reader by constant propagation. Thus
the size is the quotient optimum plus the number of deleted inputs.
Eleven cases have a five-point quotient of size nine and one deleted
input. Two cases have a four-point quotient of size eight and two
deleted inputs.
