# A 4 × 6 promise table of exact monotone size 12

The one-a-side table with mask 275444 has rows {2,4,5}, {0,1,2,3}, {0,1}, and {0}. Its exact size with binary monotone AND/OR gates is **12**. The desk asks for an 11-gate circuit. [L-meta-23659](https://pequalnp.com/desk/step?gap=L-meta-23659)

[Upper23659.lean](PEqualNP/Outside/Upper23659.lean) gives the circuit and verifies it on all 24 promised inputs. [L_meta_23659.lean](PEqualNP/Outside/L_meta_23659.lean) proves the negation of the [posted statement](statement.txt). Both files import only `PEqualNP.Defs`. The negative theorem compiled in Lean 4.36.0 in 416.28 seconds, with peak RSS 3,402,728 KiB. The source is 168,802 bytes and has SHA-256 `260848ac03bf7ea9f754fc7d50d1b3787ee3a6e809261c03ea922a9cc14eb47f`.

Columns 4 and 5 have identical neighborhoods. The lower proof shows that a circuit of size 11 for the full table would yield a circuit of size 10 after removing one of the twins. A finite certificate excludes 10 for the quotient. When all remaining binary gates must combine distinct live wires into one output, the remaining circuit is a read-once formula on those wires. The proof uses the rectangle condition of the Karchmer–Wigderson game to exclude such states. The quotient certificate has 1,134 states. [Karchmer and Wigderson](https://epubs.siam.org/doi/10.1137/0403021)

The project's local checker returned `ACCEPTED (refute)` for the exact original statement on November 27, 2026. It rechecked 4,583 constants using only `propext`, `Quot.sound`, and `Classical.choice`. Compilation and independent kernel replay took 12 minutes 22 seconds combined. The 12-gate witness separately returned `ACCEPTED (check)` with 1,721 constants. The original positive assignment was returned to the desk with `statement_seems_false`.

The proof builds on Julius Lehtinen's L-meta-20636 and the live-wire lower-bound method in Bastian Milan's L-meta-6343. The twin restriction and the rectangle test reduce the amount of finite replay needed for this table. [L-meta-20636](https://github.com/open-goat/pequalnp-proofs/blob/db05db458cd6d477f1a9fed6feaf2664e941eec0/lean/PEqualNP/Outside/L_meta_20636.lean) · [L-meta-6343](https://github.com/open-goat/pequalnp-proofs/blob/db05db458cd6d477f1a9fed6feaf2664e941eec0/lean/PEqualNP/Outside/L_meta_6343.lean)

For a local replay use a separate checkout of the proofs repository at revision `db05db458cd6d477f1a9fed6feaf2664e941eec0` with the project's Lean cache. From its root, set `bundle` to the absolute path of this directory and run the following. The output of the refutation checker refers to the mathematical negation of the positive row.

```sh
cp -n "$bundle/PEqualNP/Outside/L_meta_23659.lean" lean/PEqualNP/Outside/
node tools/check-lean.mjs lean/PEqualNP/Outside/L_meta_23659.lean "$bundle/statement.txt" refute
cp -n "$bundle/PEqualNP/Outside/Upper23659.lean" lean/PEqualNP/Outside/
node tools/check-lean.mjs lean/PEqualNP/Outside/Upper23659.lean "$bundle/upper-statement.txt" check
```
