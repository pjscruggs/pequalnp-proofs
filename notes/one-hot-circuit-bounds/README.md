# Two one-hot circuit bounds

Both circuits are evaluated on inputs with exactly one row and one column active. The two Lean files replay with Lean 4.36.0 and the Mathlib pin at [upstream revision 39ea73ce](https://github.com/open-goat/pequalnp-proofs/tree/39ea73ce33339fb5cf041c5c9ef670ade83a23d2).

## L-meta-21834 has exact monotone size nine

For the 4-by-6 table with mask 288447, [Exact21834.lean](Exact21834.lean) gives a nine-gate AND/OR circuit and excludes every such circuit of size at most eight. Rows 0 through 3 have column sets {0,1,2,3,4,5}, {1,3,4}, {1,2}, and {0}. With row indicators a,b,c,d and column indicators y₀ through y₅, one nine-gate expression is a ∨ (b ∧ (y₁ ∨ y₃ ∨ y₄)) ∨ (c ∧ (y₁ ∨ y₂)) ∨ (d ∧ y₀). The certificate provides another nine-gate witness. [Posted statement](https://data.pequalnp.com/data/lemma/L-meta-21834.52afc320b0b2.json)

The exclusion uses the finite circuit search from Julius Lehtinen's L-meta-20636, which credits Bastian Milan's L-meta-6343. A separate check by enumeration has a short justification. On either shore, an unread indicator's neighbor set must be contained in every neighbor set on that shore. This follows by fixing the opposite indicator and turning on any read indicator in a monotone circuit. All four rows and columns 0 through 4 must therefore be read. Eight binary gates can connect these nine inputs to one output only in a tree with one occurrence of each input. Enumerating OR and AND at every partition of these nine leaves gives zero matches. The Lean exclusion covers the full upstream circuit definition. [Upstream exclusion proof](https://github.com/open-goat/pequalnp-proofs/blob/a76a3433941ec978695206964c8eea8ec12de417/lean/PEqualNP/Outside/L_meta_20636.lean)

## L-meta-19373 and the fixed 128-by-128 table

[Keyed128Upper.lean](Keyed128Upper.lean) gives a 1,497-gate circuit, with 1,433 OR gates, 64 AND gates and output wire 1752. It retains the 64 products of Art Sabintsev's merged 1,500-gate witness. For their input unions, we tried adding shared subsets of two to four indicators, covered each target union with existing wires, then removed dead gates. An independent evaluator matched all 16,384 promised inputs. The 1,000-gate question remains open. [Merged construction](https://github.com/open-goat/pequalnp-proofs/pull/25872) · [Earlier 1,499-gate report](https://github.com/open-goat/pequalnp-proofs/discussions/30286) · [Assigned table](https://data.pequalnp.com/data/lemma/L-meta-19373.365dd61e2294.json)

**Keeping the 64 products costs at least 1,309 gates.** Each AND takes the OR of one prescribed set of indicators on each of its two inputs. There are 128 such sets in the merged file. For a subset S of one target set, let m(S) count targets containing S. For a singleton put D(S) = 0. For larger S, put

```text
D(S) = 1/m(S) + min [D(A) + D(S minus A)]
                        over nonempty proper A contained in S.
```

For each target, retain one path toward its output for each vertex of the OR circuit feeding it. Trim dead branches and contract unary nodes. This gives a binary tree with one leaf per distinct raw input. Charge each branching gate 1/m(S), where S is its set of descendant leaves in this tree. The physical gate can be charged only by targets that contain its full original support. Its descendant leaves in each pruned tree are a subset of that support, so its total charge across all targets is at most one. The minimum tree charge is D. Summing D over the 128 targets gives 248069/210, hence at least 1,182 OR gates. The prescribed 64 AND gates and 63 final OR gates bring the total to 1,309.

**Re-pairing at most 25 of the 64 products still costs at least 1,001 gates.** This restriction keeps the same 128 rectangle terms and changes which terms are paired, preserving a mixed OR input per rectangle half and the 64-product output arrangement. Keep the previous charges for untouched outputs. On changed outputs, project the pruned tree onto row leaves and contract unary nodes. Charge one for a branching node whose projected descendant set occurs in just that row target. The corresponding physical gate belongs exclusively to that output, since each row half appears once. Repeat on columns and average the two private charges, so each physical gate pays at most one. Changes to the pairing leave the sums of row and column private charges of the affected halves invariant. Subtract the 25 largest possible losses from the original bound to cover every choice of up to 25 changed products. The remaining OR charge is at least 1100051/1260. Its ceiling plus 127 is 1,001. At 26 changes this calculation gives 989, leaving that neighborhood unresolved.

These restrictions allow arbitrary overlap and fan-out within the OR network. The result applies to the specified rectangle construction. Other rectangle covers, uses of negation, and circuits with a different arrangement of AND and OR gates can have different costs.

## Replay

From the root of this checkout, with the pinned Lean dependencies installed, run the following commands. The Python program reads the gate list from the merged source and uses exact rational arithmetic.

```sh
python3 notes/one-hot-circuit-bounds/replay_fixed.py lean/PEqualNP/Outside/L_meta_19358.lean
cd lean
lake build PEqualNP.Defs PEqualNP.Library.Helpers.PromiseColTree
lake env lean ../notes/one-hot-circuit-bounds/Exact21834.lean
lake env lean ../notes/one-hot-circuit-bounds/Keyed128Upper.lean
```
