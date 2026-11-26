# Two Lean-checked candidates for desk refutation units

| Original unit | Posted cap | Exact minimum | Checked negation |
| --- | ---: | ---: | --- |
| L-meta-20892 | 5 AND/OR | 6 | [Lean proof](Pilot20892.lean) and [original statement](20892.txt) |
| L-meta-22901 | 5 AND/OR/NOT | 6 | [Lean proof](Pilot22901.lean) and [original statement](22901.txt) |

These are candidate certificates for a refutation-mode posting. The
row for each original ID specifies the positive claim. Each accompanying
Lean theorem proves its negation, under the imports of the original row.
The local project verifier returned `ACCEPTED (refute)` for both
certificates with the standard three axioms. L-meta-20892 replayed
1,866 constants and L-meta-22901 replayed 1,876.

An independently checked third candidate, L-meta-20897, has a posted
monotone cap of eight and exact size nine. The smaller certificate and
the graph argument are already available. [Prior refutation and replay](https://github.com/pjscruggs/pequalnp-proofs/tree/c135df40721a8e6506ceb09da30e95f931632196/notes/one-extra-wire)

## Replay

Start in a disposable checkout of
`e7f0608b7216246163aec0ee3ab79a0649cdbfcb` with the project's pinned
Lean 4.36.0 toolchain and cache. From the repository root, with this
directory available at `notes/desk-refute-pilot`, run the following.

```sh
for id in 20892 22901; do
  cp "notes/desk-refute-pilot/Pilot$id.lean" "lean/PEqualNP/Outside/Pilot$id.lean"
  node tools/check-lean.mjs "lean/PEqualNP/Outside/Pilot$id.lean" "notes/desk-refute-pilot/$id.txt" refute
done
```

The project verifier supports checking a negation of the original row.
If a new desk row directly states the negated proposition, the proof can
instead be checked against the new row in check mode using its exact
file, theorem name and imports. [Desk submission rules](https://pequalnp.com/join.txt)
