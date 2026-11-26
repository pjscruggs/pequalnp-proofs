# One NOT saves a gate on mask 842943

For L-meta-23742 the 4 × 6 graph has row masks 63, 50, 13 and 3, using least significant bits first. On the one-a-side promise, its monotone minimum is 11. Its minimum with AND, OR and NOT is 10 by exhaustive search, with a Lean-checked upper bound.

Let `S = c1 ∨ c4 ∨ c5`. The circuit outputs `r0 ∨ (r1 ∧ S) ∨ (r2 ∧ ¬S) ∨ (r3 ∧ (c0 ∨ c1))`. The one-hot condition makes `¬S` select exactly columns 0, 2 and 3. The circuit costs six ORs, three ANDs and one NOT. [Lean witness](SignedUpper.lean)

For the monotone lower bound, retaining columns 0, 1, 2 and 4 collapses two twin pairs and leaves the 4 × 4 mask 13743, whose exact nine-gate minimum is already checked. Each deleted indicator has a positive entry in a row with a negative entry. A monotone circuit must read the indicator, since omitting it would force acceptance at that negative entry. The witnesses survive either deletion. Setting each deleted indicator to false and propagating constants removes at least its first consuming gate. Conversely, one OR for each twin pair lifts a nine-gate witness to eleven. [Checked quotient](https://github.com/open-goat/pequalnp-proofs/pull/12516) · [Path-family classification](https://github.com/open-goat/pequalnp-proofs/discussions/37052)

## Replay

From the upstream checkout’s `lean/` directory, with the pinned Lean 4.36.0 toolchain and built dependencies, run `lake env lean ../notes/842943-negation/SignedUpper.lean`. This checks the gate conventions, the size and all 24 promised evaluations. The replay used the definitions root at `7e46f41504f47cca795d80ac554db9bdf8baa454`.

For the lower-bound replay, each signal is its 24-bit truth table. Any accepted cell and rejected cell must be distinguished by some input of the output cone. Checking all input subsets gives eight distinguishing subsets of size seven and none smaller. A connected circuit reading seven inputs needs at least six binary gates, so a nine-gate candidate has at most three NOT gates. Constants, copy gates, and duplicate semantic signals can be eliminated without increasing either gate count.

The search starts with each distinguishing input subset permitted by the gate budget. At each step it lists every gate that can read the available signals and every choice of which operands still have future uses. It retains at most one more signal than there are gates left. It prunes a state if some accepted/rejected pair has equal bits on every available wire. Once no NOT gates remain, that condition strengthens to requiring a wire that is true on the accepted cell and false on the rejected cell. The search memoizes the available truth tables and remaining budgets. The signed lower bound uses this C++ replay.

From this folder, build and run the replay.

```sh
c++ -std=c++20 -O2 -Wall -Wextra -pedantic replay.cpp -o replay
./replay 10 0
./replay 9 3
./replay 10 1
```

The monotone exclusion makes 15,436 recursive calls and memoizes 3,973 failures. The signed exclusion starts with 45 distinguishing subsets, makes 6,913,374 recursive calls, and memoizes 1,907,714 failures. The final run prints a ten-gate signed witness as operations on truth-table words.

Jukna’s discussion of cross-side graph representation in §3.4–3.5 gives the model and explains the role of rectangle covers for depth-restricted circuits. The replay enumerates shared gates at arbitrary depth. [Jukna, *Disproving the Single Level Conjecture*](https://web.vu.lt/mif/s.jukna/ftp/single1.pdf)

The same two-deletion argument transfers previously checked square exclusions to 187 posted rectangular caps. [Sweep and replay](twin-sweep/README.md)
