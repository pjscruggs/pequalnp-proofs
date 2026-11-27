# Complementing small one-hot graphs

For the fan-in-two AND/OR model in L-meta-25454 and L-meta-25455, exhaustive finite search gives the following sharp bounds. Write μ(G) for the minimum number of gates on inputs consisting of exactly one row pin and one column pin. An edge (i,j) occupies bit ni+j of the mask. The displayed complement mask is the least mask in its symmetry class.

| Side n | Labeled graphs | Classes | Maximum μ(complement G) − μ(G) | Example and costs |
| ---: | ---: | ---: | ---: | --- |
| 3 | 512 | 26 | 2 | Single edge, mask 1 (1 gate), complement class 255 (3 gates) |
| 4 | 65,536 | 192 | 4 | Matching, mask 4680 (7 gates), crown class 31710 (11 gates) |

This checks the proposed bound of 2n − 4 for both sizes, including constant graphs. The atlas already reports per-class computations and separate kernel checks. The tables here pair the costs under complementation. These are computational minima. The general conjecture remains open. [Prior atlas and kernel coverage](https://github.com/open-goat/pequalnp-proofs/discussions/12311) · [Related complement-transfer construction](https://github.com/open-goat/pequalnp-proofs/discussions/25864) · [Matrix complexity literature discussed with the atlas](https://github.com/open-goat/pequalnp-proofs/discussions/12311#discussioncomment-19894147)

## Eliminating repeated rows and columns

Suppose G has two identical rows and two identical columns. Delete one row and one column from those pairs to form H. Then

    μ(H) ≤ μ(G) ≤ μ(H) + 2.

For the first inequality, restrict a circuit for G by setting the two deleted pins to false. Each promised input for H now embeds into a promised input for G. Propagate constants through AND and OR, bypass unary copies and relabel the surviving pins. If the output simplifies to false, use a missing output with zero gates. If it simplifies to true, use an empty AND. In that case the source must already have at least one gate when H has side at least two, since no raw pin is true on every retained pair. Thus neither constant case increases the gate count.

For the second inequality, prepend one OR of the two row pins and one OR of the two column pins. Feed these into the retained row and column inputs of a circuit for H. The equalities of the corresponding neighborhoods ensure that it computes G on every promised pair. Reindex earlier gate outputs and preserve any missing output by choosing a fresh out-of-range index.

The complement has the same duplicate pairs, and deleting them gives the complement of H. Hence

    μ(complement G) − μ(G) ≤ μ(complement H) − μ(H) + 2.

The proposed allowance increases by exactly two per side increment. Thus a smallest counterexample has side at least five, and on at least one shore all neighborhoods must be distinct. In particular a search at side five may skip every graph with both a repeated row and a repeated column. The argument also applies to the opposite orientation by complementing G. This is a written reduction.

## Replay

Run in this directory with a C++20 compiler and Python 3.

```sh
g++ -O3 -std=c++20 frontier.cpp -o frontier
python complements.py 3 ./frontier replay-3.tsv
python complements.py 4 ./frontier replay-4.tsv
```

Compare the rows with [side three](complements-3.tsv) and [side four](complements-4.tsv). The final column gives the greatest excluded budget, with −1 for minimum zero. A raw pin or a missing output costs zero. A missing output evaluates to false. An empty AND costs one and yields true. No zero-gate output yields true everywhere for these side lengths. For a nonconstant target, constant intermediates and unary gates can be simplified away. [Circuit evaluation](https://github.com/open-goat/pequalnp-proofs/blob/ec5c3b478f6e7f802dae6582b0feae5cf1a378c1/lean/PEqualNP/Defs/CircuitLowerBounds.lean) · [ReadsBack](https://github.com/open-goat/pequalnp-proofs/blob/ec5c3b478f6e7f802dae6582b0feae5cf1a378c1/lean/PEqualNP/Defs/NestedCoverCircuit.lean)

Adjacent row swaps and transposition generate all row and column permutations and shore exchange. Each relabels the input pins invertibly while preserving the gate list length. The driver enumerates the full orbit of every representative and tests budgets upwards. It fails on a search cutoff and checks each returned witness cell by cell.

The search starts with each subset of raw inputs that can feed a connected output cone within the budget. At each binary gate it can retain either, both or neither operand for reuse. With k gates remaining, at most k+1 live wires can still join into one output. A successful live set must also distinguish every positive cell from every negative cell in the forward direction: some wire is true at the positive cell and false at the negative one. Entrywise monotone gates preserve the coordinatewise order, so this condition is necessary. Equal live tables can share a wire. [Related checked live-wire search](https://github.com/open-goat/pequalnp-proofs/pull/12547)
