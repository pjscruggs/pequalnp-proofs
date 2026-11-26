# Exact six-gate minima for 33 additional cases

The 33 distinct six-point tables in this extension each require exactly **six** AND/OR/NOT gates on the signed two-lit promise. Each case has a Lean refutation of its original five-gate statement and a matching Lean-checked six-gate witness. They are all in the earlier 471-row computational audit. Together with the earlier checked case L-meta-22784, this evidence branch contains 34 exact minima from that audit. [Case manifest](cases.tsv) · [Earlier audit and checked example](../README.md)

The case manifest gives the exact mask, excluded cap, minimum, source file, and SHA-256 of the original guarded Lean statement encoded as UTF-8 without a trailing newline. The `lower/` files preserve the original proofs and attribution to the live-wire engine from Bastian Milan's L-meta-6343. The proof method follows the signed adaptation in the original audit, which also credits Julius Lehtinen's L-meta-20636 monotone adaptation. [Original live-wire proof](https://github.com/open-goat/pequalnp-proofs/pull/12547) · [Monotone adaptation](https://github.com/open-goat/pequalnp-proofs/pull/27751)

[Upper.lean](Upper.lean) checks every witness against all 36 ordered pairs, including repeated points, in the upstream evaluator. An independent scalar pass checks the same ordered pairs and that every gate reads only earlier wires. [Numeric gate lists](witnesses.json) use `0` for AND, `1` for OR, and `2` for NOT. A NOT uses the first operand. Wires `0` through `5` are the inputs and the six gate outputs are wires `6` through `11`.

All statements were posted in prove mode. For 29 cases the desk acknowledged a `statement_seems_false` release after local checking. Four mathematical results were checked after the desk had already acknowledged `other` releases. Those cases are L-meta-22763, L-meta-22821, L-meta-22884, and L-meta-22889. No case in the extension represents an accepted desk proof.

## Replay

From the checkout's `lean/` directory, with the pinned Lean 4.36.0 toolchain and built `PEqualNP.Defs` dependencies, run:

```sh
lake env bash ../notes/signed-two-lit-desk-audit/exact-followup/verify.sh
```

The script compiles and independently kernel-replays each lower bound and the aggregate witness module. It uses a temporary build directory. Set `JOBS=2` to replay two lower bounds at a time.
