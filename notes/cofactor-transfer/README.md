# Reuse a checked five-input circuit theorem on a six-input child

If a five-input monotone truth table has a proof that counted NOT gates save no gates, four AND/OR extensions inherit the result. One can combine the fresh variable with the **output**, or combine it with an **essential input** before running the parent's circuit. An unused input also preserves the result. The Lean theorems work at every positive parent arity. The generator below takes concrete five- and six-input tables, finds a transfer under input permutations, and emits the specialization. Lean checks the permutation and every one of the 64 child assignments.

The input-pair proof inserts one counted gate ahead of the parent circuit. For the lower direction, fixing the fresh input to the neutral value recovers the nonconstant parent and eliminates a gate. For output padding the gate is appended instead. The proof uses the project's existing gate-elimination and wire-relabeling lemmas. [Original discussion and references](https://github.com/open-goat/pequalnp-proofs/discussions/19533)

## Generate a proof

In hexadecimal tables the value at assignment `a` is bit `a`. Input wire `i` has value bit `i` of the assignment. Here are two specializations of parent L-meta-8664. The first combines a new wire with the output. The second replaces an input by its AND with a new wire.

```sh
python3 instantiate.py 0xeac8e080 0xfeeefaeafeaaeaaa --parent-gap 8664 > OutputExample.lean
python3 instantiate.py 0xeac8e080 0xeac8e080c0c0c000 --parent-gap 8664 > PairExample.lean
```

Without `--parent-gap` the generated theorem is conditional on the parent no-saving statement. Supplying the parent gap instantiates it with the merged theorem. The output files are for research builds. An official submission has to satisfy the desk's one-file and permitted-import rules for that particular gap. The five-input contributors retain credit for their original certificates.

## Reproduce

Start from a checkout of this branch with the repository's pinned Lean and Mathlib. From the `lean` directory, run the commands below with Python 3.10 or later. Add `--all` to both invocations of `replay.py` to build and check all 21 published transfers. The default checks all five mechanisms, the original nine-gate witness, and its lower bound.

```sh
lake exe cache get
lake build $(python3 ../notes/cofactor-transfer/replay.py --modules)
lake env python3 ../notes/cofactor-transfer/replay.py
```

The parent certificates include expensive kernel computations. Their compiled modules can be reused for additional children. Once dependencies are built the transfer itself checks a small truth table. `examples.json` records the child ID, 64-bit child table, parent ID and 32-bit parent table for each of the 21 transfers. To rerun the permutation-class census use `python3 six_input_filter.py` from this directory.

In the audit, all 21 generated proofs compiled against their original parent theorems and reported only `propext`, `Classical.choice`, and `Quot.sound`. Both occurrences of each truth table in the merged child statement matched the recorded 64-bit value. The separate census replay reproduced 286,740 labeled tables, 1,399 permutation classes admitting a reduction, and 7,574 residual classes after permutation and duality.

## Where to apply it

All 21 original child rows now have merged proofs. The accepted proof for L-meta-13105 was opened before the discussion. Another merged example, L-meta-13223, explicitly credits the five-input work on L-meta-8678 for its restriction machinery. This package makes the transfer reusable for future rows. A screen of the public November 25, 2026 20:16 UTC data found 31 matches among 504 positive six-input targets and 132 checked five-input records. All 31 already had a PR or had left the open desk. The scan included input permutations and parent duals. The generator implements permutations and the five transfer mechanisms described above. [Worked example's accepted PR](https://github.com/open-goat/pequalnp-proofs/pull/17418) · [Another merged restriction proof](https://github.com/open-goat/pequalnp-proofs/blob/1d2a1d1a2b6b2ac85eaac911fd0bcf32a89695a9/lean/PEqualNP/Outside/L_meta_13223.lean)
