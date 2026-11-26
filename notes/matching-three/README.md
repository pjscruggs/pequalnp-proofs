# Exact monotone circuit size of 3 × 3 perfect matching

L-meta-17390 asks for 13 binary AND/OR gates to decide perfect matching on
the nine edge indicators. The exact size is **14**. The cap-13 replay
exhausts 602,209 live-frontier calls. A separate Python implementation
excludes the same cap. The included 14-gate witness is evaluated on all
512 inputs. [Desk step](https://pequalnp.com/desk/step?gap=L-meta-17390)

```sh
c++ -std=c++20 -O3 matching-shard.cpp -o matching-shard
python3 verify.py ./matching-shard
```

The target is monotone, so agreement on the six minimal positive graphs
and the fifteen maximal negative graphs decides agreement everywhere.
Each of the nine indicators is essential, as a permutation matrix
containing that edge becomes negative when the edge is deleted. After
trimming dead gates and merging duplicate truth words on the 21 cared
inputs, a normalized circuit gives a sequence of live frontiers
starting with all nine inputs. Each AND or OR appends its truth word
and either operand can be discarded after its last use. The search
enumerates those cases and checks that every positive-negative pair
still has an earlier live wire separating it in the forward direction.
When the remaining gates are fewer than the number of live wires minus
one, no output cone can use all those live wires. This gives the budget
pruning condition. The foundational Lean frontier method is due to
Bastian Milan. [Checked live-wire proof](https://github.com/open-goat/pequalnp-proofs/pull/12547)

A 14-gate upper witness was previously reported with a Lean build by
another team. Here each branch fixes one of the three first-row
matches and computes the two possible completions with two ANDs,
one OR, and the final AND for the fixed edge. Combining the three
branches uses two further ORs. Earlier work also excluded the
at-most-three-AND shard by an overapproximation with arbitrary
OR networks. The present finite exclusion covers all four AND-count
ranges of the monotone 13-gate job. [Prior 14-gate witness](https://imd-explorer.up.railway.app/jobs/71f09f9e-5878-4ff3-bfb7-97af5d716e09) · [Prior shard exclusion](https://github.com/open-goat/pequalnp-proofs/discussions/21642#discussioncomment-19925884)
