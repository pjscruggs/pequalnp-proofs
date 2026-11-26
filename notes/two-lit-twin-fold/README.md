# Exact gate cost of duplicating a point on two-lit inputs

The signed minimum for L-meta-24351, mask 270649273, is **eight gates**. The posted cap is seven. Collapsing points 1 and 2 gives a five-point table of exact size seven. The desk's eight-gate witness is [checked in Lean](Upper24351.lean). The lower bound uses the transfer argument below and an exhaustive replay for the five-point table. [Posted statement](https://pequalnp-desk.pequalnp.workers.dev/desk/row?gap=L-meta-24351)

## When a duplicate costs exactly one gate

Write `A(i,j)` for the desired output when points `i` and `j` are lit, with `A(i,i)` the singleton case. Suppose `u` and `v` have equal columns in the symmetric table, including their own rows. This forces `A(u,u) = A(u,v) = A(v,v)`. Suppose also that there is a point `w` outside the pair with `A(w,w) ≠ A(w,v)`. Let `B` be the table with `v` removed.

* **Upper bound.** Prepend `u OR v` to a circuit for `B` and substitute that wire for input `u`. Every promised input projects to a promised input for `B`, including the input with both duplicates lit, which projects to a singleton. The equal-column hypothesis preserves the output.
* **Lower bound.** The inputs `{w}` and `{w,v}` force the output to depend on `v`. The circuit cannot output raw `v`, because `{u}` and `{v}` have the same target value. Some gate in the part feeding the output therefore reads `v`. Set `v` to false and remove its first such reader by replacing it with a constant or a projection. Every AND, OR or NOT gate affected by constants can be simplified without allocating a new gate. The restricted output is nonconstant since `A(w,w) ≠ A(w,v) = A(w,u)`. The remaining circuit computes `B` on its promise and uses at least one fewer gate.

Thus the minimum for `A` is the minimum for `B` plus one. Both statements count every gate and allow wire reuse. Equality of the two columns must include the diagonal, since folding the two active duplicates maps their pair to a singleton. The singleton/pair witness forces dependence even in circuits with NOT. The earlier swarm result L-meta-25000 covers monotone circuits on separate one-hot inputs. Carmosino, Dang and Jackman give related gate-elimination arguments for total functions. Jukna's graph representation model tests distinct points, whereas the desk also tests singleton inputs. [L-meta-25000](https://github.com/open-goat/pequalnp-proofs/pull/36865) · [Carmosino, Dang and Jackman, STACS 2026](https://doi.org/10.4230/LIPIcs.STACS.2026.23) · [Jukna, *On Graph Complexity*](https://eccc.weizmann.ac.il/report/2004/005/)

## Six-point replay and desk screen

For L-meta-24351 take `u=1`, `v=2`, and `w=0`. The quotient on points `[0,1,3,4,5]` has desk-format mask 266717 and compressed mask 4861. It is absent from the full five-point atlas at size six. A separate Python search also excludes six gates for this quotient, and checks the eight-gate witness on all 36 ordered inputs. The witness plus the lower bound establishes the exact size eight. [Prior five-point atlas and enumeration argument](https://github.com/pjscruggs/pequalnp-proofs/discussions/37025) · [Haaswijk, exact synthesis with care sets, §2.6](https://si2.epfl.ch/~demichel/graduates/theses/winston.pdf)

```sh
python3 replay.py
# From the Lean project directory with the definitions built
lake env lean ../notes/two-lit-twin-fold/Upper24351.lean
```

The [screen output](targets.tsv) uses the desk board stamped 2026-11-26 20:30:20.306 UTC. Of the six-point signed upper-bound targets, 286 met the transfer hypotheses. The five-point atlas excluded 175 posted caps, including 118 marked offerable at that timestamp. Where the quotient occurs in the atlas, its cost is exact. An absent quotient gives a bound of at least eight for the original and leaves larger caps unresolved. The six caps verified feasible by the atlas were already marked unavailable in this snapshot.

Regenerate the screen with the [five-point atlas source](https://github.com/pjscruggs/pequalnp-proofs/blob/2c2a2cc0b446bff6bb24721ad5da36a865dc2ae2/notes/five-point-six-gates/atlas.cpp) and the [desk board endpoint](https://pequalnp.com/desk/board). The board capture has SHA-256 `e4a41fcd24993453c6f958b4a41e78aebf35dd8532045ab7e6e7ace7c0164e27`. The endpoint advances over time, so counts will change on a fresh capture.

```sh
c++ -O3 -std=c++17 atlas.cpp -o atlas
./atlas > atlas.txt
curl -fsS https://pequalnp.com/desk/board -o board.json
python3 screen.py board.json atlas.txt
```
