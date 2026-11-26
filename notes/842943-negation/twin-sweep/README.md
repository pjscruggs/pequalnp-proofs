# Transferring checked square minima to rectangular desk tables

The November 26 desk board at 20:35:47 UTC lists **187** monotone 4 × 6 proof units whose caps are one gate below a lower bound obtained from a checked 4 × 4 core. The sweep covers 32 core classes up to row and column permutation and transposition. Of the 187 units, 112 were offerable, including 105 outside the published path sweep. [Result table](results.tsv) · [Earlier path sweep](https://github.com/open-goat/pequalnp-proofs/discussions/37052)

Retain one representative of each of a table's four distinct column types. The replay requires each deleted column to have a 1 in a row with a 0 in a retained type. A monotone circuit must read that indicator, since omitting it would force acceptance at the 0. Pinning the indicator to false and simplifying eliminates a gate. Repeating for the second deleted column gives the checked square lower bound plus two. When the square theorem also gives a matching upper bound, two ORs lift that upper bound back, yielding equality on the original table.

For example, L-meta-22191 asks for at most 12 gates for mask 842940. The collapsed mask is 13740, whose checked lower bound of 11 gives a lower bound of 13 before the deletions. For L-meta-23742, the checked exact cost of 9 for mask 13743 gives an exact cost of 11 before the deletions. [L-meta-8971](https://github.com/open-goat/pequalnp-proofs/blob/7e46f41504f47cca795d80ac554db9bdf8baa454/lean/PEqualNP/Outside/L_meta_8971.lean#L3523) · [L-meta-6299](https://github.com/open-goat/pequalnp-proofs/pull/12516)

From an upstream clone, fetch the path-sweep revision so that the replay can identify overlapping desk IDs. Then run the script from the evidence checkout with `--repo` pointing to that clone.

```sh
git -C /path/to/pequalnp-proofs fetch https://github.com/pjscruggs/pequalnp-proofs.git a92151c18085dd4e96a72abc15d4ad61b14b7344
python -B notes/842943-negation/twin-sweep/sweep.py --repo /path/to/pequalnp-proofs --output /tmp/twin-sweep.tsv
```

The board file preserves the ID, title, kind and availability for all 386 posted 4 × 6 monotone prove units at that capture time. The sweep matches explicit negative `RepSizeAtMost` clauses from checked Lean statements at revision `7e46f41504f47cca795d80ac554db9bdf8baa454`. Each result names the original source file and line. [Desk-board projection](desk-board.json)
