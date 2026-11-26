# A gate lower bound from non-biclique components

Let \(G\) be a bipartite graph with no full row or column. Let \(e\) be its number of nonisolated vertices and \(b\) its number of connected components that contain an edge and are not complete bipartite. A monotone fan-in-two AND/OR circuit representing \(G\) on the one-a-side promise has at least

\[
e-1+\left\lceil b/2\right\rceil
\]

gates. Disjoint unions of two or more four-vertex paths attain this bound. The proof extends the read-once test from the parent discussion to arbitrary sharing.

**Read-once case.** On the all-zero assignment and on every singleton, the circuit outputs zero. Every singleton extends to a promised nonedge, so this follows by monotonicity. Every nonisolated indicator is essential, by comparing an incident edge with the singleton at its other endpoint. The arguments below only need the circuit's singleton-zero property, which is preserved when inputs are fixed to zero.

In a read-once monotone formula with zero on all singletons, flatten the top ORs. The endpoints of every positive pair must occur in the same top branch, on opposite children of that branch's first AND. Connectivity then puts every nontrivial component in one branch, with one shore per child. Every component vertex is accepted as a singleton by its child, so the component is complete bipartite.

**The number of repeated wire uses.** Simplify constants and unary gates, replace repeated arguments by a single argument, and trim to the output cone. An invalid input wire in the Lean circuit model is a constant zero and is handled by the same simplification. Write \(g\) for the remaining gate count and \(n\) for the number of raw input wires in the cone. In the nonconstant case every gate is binary. With \(2g\) wire occurrences and \(n+g-1\) non-output wires, the number of occurrences in excess of one use per non-output wire is

\[
q=\sum_{w\ne\mathrm{output}}(\operatorname{outdeg}(w)-1)=g-n+1.
\]

Equivalently \(q\) is the cycle rank \(E-V+1\) of the connected undirected wire multigraph. We show that \(b\le 2q\) for any represented graph when the circuit is zero on singletons. The case \(q=0\) is read-once.

**Remove the inputs of a first reused wire.** In topological order, take the first wire \(s\) with \(d\ge2\) uses. The subcircuit computing it is a read-once formula \(S\) on a set \(T\) of raw inputs. If \(s\) is raw, then \(S\) has one leaf and no gate. No input in \(T\) has a path to the output bypassing \(s\), since such a second path would fork at an earlier reused wire. The output therefore has the form \(R(S,\ldots,S,X)\) with all \(d\) occurrences set to the same bit and \(X\) the remaining inputs.

If there is a positive pair with both endpoints in \(T\), the monotone map \(t\mapsto R(t,\ldots,t,0)\) is the identity. It maps zero to zero by constant-free evaluation, and the internal edge forces its value at one. Thus \(S\) is zero on all singletons, and no positive pair crosses from \(T\) to \(X\). Each component meeting \(T\) is represented by the read-once \(S\) and is a biclique.

If there is no positive pair within \(T\), every nonisolated vertex of \(T\) has an outside neighbor. Its singleton makes \(S=1\), since otherwise its edge could not be distinguished from the outside singleton. Hence all nonisolated vertices of \(T\) on a given shore have identical neighborhoods. Each shore of \(T\) meets at most one nontrivial component. In either case, at most two non-biclique components meet \(T\).

Now set \(T=0\), making \(s=0\). Removing the private subtree at \(s\) deletes one fewer internal edge than vertices, then removes the \(d\) outgoing edges of \(s\). The rest remains connected before constant propagation because every surviving wire still has a path to the output and these paths cannot enter the private subtree. Its cycle rank is \(q-d+1\). Propagating zeros cannot increase cycle rank. A gate forced to zero and its incident wires are deleted, a gate reduced to an identity is contracted to its live predecessor, and any duplicate occurrences or unused branches are deleted. Cycle rank does not increase under deletion or contraction. If the whole output becomes zero, there are no remaining positive pairs. Otherwise the resulting circuit still has zero on singletons and cycle rank at most \(q-1\). Every original component disjoint from \(T\) survives intact. By induction, at most \(2(q-1)\) such components can fail to be bicliques. This proves \(b\le 2q\). Since \(n\ge e\), the claimed gate lower bound follows.

**Tightness on disjoint paths.** The four-gate expression `((a OR b) AND x) OR (a AND y)` represents the component with edges \(ax,ay,bx\) and is zero on singletons, so it can be used for an unpaired path. For two disjoint paths use rows \(a,b,c,d\), columns \(x,y,z,w\), and edges \(ax,ay,bx,cz,cw,dz\). Define \(S=a\lor z\), \(B=b\lor w\), \(C=x\lor c\), and \(D=y\lor d\). The circuit

```text
((S OR B) AND C) OR (S AND D)
```

uses eight gates including those definitions. The first product contributes \(ax,bx,cz,cw\), and the second contributes \(ay,dz\). All other products select two indicators on the same shore and vanish on the promise. This is the 4-by-4 mask 19475. For \(k\) disjoint four-vertex paths with \(k\ge2\), group the paths into pairs and, if needed, one singleton. Compute each group with the circuit above and OR their outputs. The count is \(4k+\lceil k/2\rceil-1\), which matches the lower bound since \(e=4k\) and \(b=k\). Three paths give mask 17986273347 and exact size 13.

Jukna's graph-representation model specifies all two-active-indicator pairs, including those within a shore. The eight-gate construction uses that within-shore pairs are unconstrained on the one-a-side promise. [Jukna, *On Graph Complexity*](https://eccc.weizmann.ac.il/report/2004/005/)

## Desk application and evidence

The desk's L-meta-20897 asked for eight gates on mask 35228. All nine indicators are essential. Rows 0 and 1 and columns 2 and 4 form an induced four-vertex path, so the read-once argument already rules out eight. The [previous screen](https://github.com/open-goat/pequalnp-proofs/discussions/36974) classified this instance. The new instance-specific Lean replay proves both the nine-gate upper bound and the negated eight-gate cap. The desk accepted release as `statement_seems_false` and no refutation step was posted at that check.

From this directory, run `python check_witnesses.py` for three upper-bound controls. With the repository's pinned Mathlib cache in place, run `bash replay.sh` to build the definitions and independently recheck the exact-nine theorem. The general component bound above is a mathematical proof, not part of the Lean theorem.

## Model and prior work

Jukna's [On Graph Complexity](https://eccc.weizmann.ac.il/report/2004/005/) requires correctness on every pair of distinct vertex indicators, including same-shore pairs. The eight-gate construction above uses the narrower promise essentially. The P4 obstruction for total positive read-once functions is classical, as described by [Golumbic, Mintz and Rotics](https://doi.org/10.1016/j.dam.2008.02.011). The count and the single repeated wire decomposition are applied here to a partial function on the one-a-side promise.
