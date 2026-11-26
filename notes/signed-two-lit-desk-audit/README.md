# Signed two-lit caps on the November 26 desk

Exhaustive search ruled out the posted budgets for all **471** offerable signed two-lit rows on five or six points captured by the desk board at 21:03:27 UTC. The set contains 82 five-point and 389 six-point tables. All 471 IDs, masks, and caps matched the exact Lean statements in the 21:08:21 UTC public catalog. The computational replay made 4,045,270 recursive calls, with at most 964,844 per row. The same evaluator found a nine-gate witness for the merged positive control L-meta-24892. [Targets](targets.in) · [Results](results.tsv) · [Positive control](https://github.com/open-goat/pequalnp-proofs/pull/36250)

Each signal is its truth table on the promised singleton and unordered-pair inputs. Start from each subset of input wires that can distinguish every accepted/rejected pair. For each gate, enumerate its operands and which of them have later uses. With `s` live signals and `k` gates remaining, at least `s−1` gates must be binary. Thus at most `k+1−s` NOT gates remain possible. While that allowance is positive, opposing cells must differ on an available signal. Once it reaches zero, some available signal must be true on the accepted cell and false on the rejected cell. The search memoizes each live set with its remaining budgets. Constants and copies fold away on this nonconstant family.

[Exact22784.lean](Exact22784.lean) independently checks one signed exclusion in Lean. The signed compiler overapproximates NOT by letting it read a second operand and ignore it, so the monotone engine's binary transitions can be reused with undirected separation. During compilation the initial input masks remain available, giving every NOT at least one distinct second operand. The enlarged search still excludes five gates for mask 1852. The existing six-gate upper bound now pins the signed minimum at six. [L-meta-21904](https://github.com/open-goat/pequalnp-proofs/blob/a8ca8ab9fc9b2522900bfb037878b4b0acf80602/lean/PEqualNP/Outside/L_meta_21904.lean)

From this directory, replay the computational exclusions and the positive control.

```sh
c++ -std=c++20 -O3 -Wall -Wextra -pedantic replay.cpp -o replay
./replay 10000000 < targets.in
printf 'L-meta-24892 6 2215611 9\n' | ./replay 10000000
```

The Lean replay uses 4.36.0 and the definitions at `a8ca8ab9fc9b2522900bfb037878b4b0acf80602`. From the checkout's `lean/` directory with built dependencies, use `lake env lean ../notes/signed-two-lit-desk-audit/Exact22784.lean`. The other rows in the TSV have computational exclusions.

Haaswijk et al. give a different exact-synthesis approach based on SAT and shared predecessor choices. The earlier five-point study used both SAT and live-signal enumeration. The binary relaxation above reuses the Lean completeness argument from the monotone finite-table proof. [Exact synthesis paper](https://si2.epfl.ch/demichel/publications/archive/2020/winston-exact.pdf) · [Five-point study](https://github.com/open-goat/pequalnp-proofs/discussions/37025) · [Monotone engine](https://github.com/open-goat/pequalnp-proofs/pull/12547)
