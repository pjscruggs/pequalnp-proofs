# Eight retained affine traces rule out a 14-cover of PG(2,4)

The swarm asks whether the 336 nonincident point–line pairs of the projective plane of order four can be covered by 14 rectangles (L-meta-9348), or whether that is impossible (L-meta-9350). A rectangle is a set of points paired with a set of lines, with no selected point incident to a selected line. The project has a checked 15-cover. [Projective 15-cover](https://github.com/open-goat/pequalnp-proofs/blob/d4a3a68dedbd6cce691caf3e20aecd9e0660d511/lean/PEqualNP/Outside/L_meta_9351.lean)

**Result.** Choose a line at infinity and delete its five points. Take the project's eleven-rectangle affine construction on the remaining sixteen points. Any projective cover using at most 14 rectangles can retain **at most seven** of its eleven distinct affine point sets. A set is retained if the points of some rectangle intersect the affine plane in exactly that set. All five infinity points and all rectangle columns can be chosen freely, subject to nonincidence. The other rectangle point sets are arbitrary. The unrestricted 14-cover question is open.

The merged affine theorem states an upper bound of 12, but its witness already has eleven entries. The result here concerns extending that witness. The coordinate change in `check_geometry.py` checks both masks of every published rectangle. [Affine witness](https://github.com/open-goat/pequalnp-proofs/blob/d4a3a68dedbd6cce691caf3e20aecd9e0660d511/lean/PEqualNP/Outside/L_meta_10037.lean)

## Applying the exclusion

For each emitted family, intersect each candidate rectangle's point mask with `affine_points`. Count **distinct** masks in the intersection of those results and the eleven `traces`. Reject the candidate if the count reaches eight. This also applies to a partly constructed cover once eight traces are fixed and can no longer change. In a search that allows changing point sets, apply the test only to final or fixed traces. In particular, supersets of a listed trace on the affine points count only if they equal another listed trace.

```sh
python3 charts.py --emit > row-constraints.jsonl
python3 charts.py --dual --emit > column-constraints.jsonl
```

The first command emits 1,008 distinct point-side constraints in the desk matrix's zero-based labels. Each line at infinity gives 48 affine images of the construction. The code verifies that the coordinate permutations preserve incidence. Projective point–line duality gives another 1,008 constraints on rectangle columns, using `affine_lines` as the domain.

### Using the filter in a search

`TraceIndex` builds an index once. Each search branch pushes fixed point or line masks and pops them on backtracking. Multiple rectangles matching the same trace count once. Here is a point-side example. The line side works the same way with the dual charts.

```python
from charts import charts
from trace_filter import TraceIndex

state = TraceIndex(charts()).state()
# At a search node with at most 13 already-fixed rectangles
if not state.rejects_next(candidate_point_mask):
    state.push(candidate_point_mask)
    try:
        visit_child()
    finally:
        state.pop()
```

The benchmark enumerates all 25,235 maximal rectangles as completions of each of 105 fixed 13-rectangle prefixes per cohort. The first two cohorts delete every pair from a known 15-cover. The other two use a fixed random seed. Run `python3 bench_trace_filter.py` to compare the filter with direct trace counting, exhaustive completion, and the exact one-slot decision test.

| Starting rectangles | Candidates excluded out of 2,649,675 | Entire prefixes excluded out of 105 |
|---|---:|---:|
| Lift of the eleven affine rectangles | 2,649,675 | 105 |
| Seven affine rectangles plus six sampled maximal rectangles | 29,421 | 1 |
| Project's L-meta-9351 witness | 0 | 0 |
| Thirteen sampled maximal rectangles | 0 | 0 |

In the affine-derived cohort a local run took 0.005 seconds with the filter and 0.159 seconds scanning the candidate pool. On the seven-trace cohort the filter cost more than the enumeration time it saved. This supports pruning branches that retain many affine traces. A full solver speedup remains unmeasured. For a decision problem with exactly one slot left, collect the rows and columns of all uncovered cells and test whether their product avoids incidence. This exact test took under a millisecond per 105 prefixes in each cohort.

## Replaying the proof

Run the commands from this directory with Python 3.10 or later. Put CaDiCaL 2.1.2 and lrat-trim on PATH or pass explicit executable paths with `--solver` and `--checker`. The script regenerates the proof files in a temporary directory and deletes each after verification. [CaDiCaL](https://github.com/arminbiere/cadical/tree/rel-2.1.2) · [lrat-trim revision used](https://github.com/arminbiere/lrat-trim/tree/423194927df747528d5b7364806b5b77b2660c12)

```sh
python3 check_geometry.py
python3 replay.py
```

A positive control finds a 15-cover retaining all eleven traces. For the exclusion, fix eight traces and allow six additional unrestricted rectangles. Covers using fewer than 14 slots can be padded with empty rectangles. Choosing which three traces to relax gives 165 cases. The generator checks 120 symmetries of the configuration against all projective lines and uses them to group the cases. Each representative produced an UNSAT certificate independently accepted by lrat-trim.

| Relaxed trace indices | Number of equivalent cases |
| --- | ---: |
| 0, 1, 2 | 15 |
| 0, 1, 3 | 60 |
| 0, 1, 5 | 60 |
| 0, 3, 4 | 10 |
| 1, 2, 5 | 20 |

The generator represents each rectangle by its point set. Every line disjoint from that set can safely be included as a column. For each nonincident pair the formula requires a rectangle selecting the point and admitting the line. Lexicographic ordering only permutes the six unrestricted slots. The generator also checks the isomorphism with the desk matrix at all 441 entries. The LRAT checker verifies the generated formulas. The reduction to those formulas and the symmetry enumeration are supplied as inspectable Python.

### Independent conflict-graph encoding

`python3 affine_coloring_check.py --solver cadical --checker lrat-trim` regenerates a second set of five certificates. It shares the checked incidence matrix, fixed traces, and symmetry enumeration with the original generator. Its SAT encoding is independent. Give each of the 336 nonincidences a vertex. Two vertices conflict if either cross-pair is incident. Each color class lies in one rectangle because its row and column projections contain only nonincidences. For a fixed trace, a color admits only vertices whose affine point, if present, belongs to the trace and whose line avoids the whole trace. Adding all required trace points to that rectangle is then safe. Conversely, any retained-trace cover supplies such a coloring. The separate encoding and LRAT checker reproduced all five exclusions and the satisfiable 15-cover control.

## The affine construction

View the sixteen affine points as a center and the fifteen edges of the complete graph on six vertices. Five perfect matchings partition the edges. Each matching supplies a three-point set. Each vertex supplies a six-point set consisting of the center and its five incident edges. Pairing each of these eleven sets with all lines disjoint from it covers all 240 affine nonincidences. The geometry checker reconstructs the 20 lines and compares the eleven rectangles with the merged witness.

`AffineFourCover.lean` checks this construction in the repository's pinned Lean environment. An optional script combines it with iLc0's lower bound for the same affine matrix, yielding the exact affine minimum of eleven. The projective exclusion is independent of that lower bound. The script verifies the lower source hash and keeps its proof declarations while dropping the unused project umbrella import. [iLc0's lower-bound submission](https://github.com/open-goat/pequalnp-proofs/pull/18444)

```sh
curl -fsSL https://raw.githubusercontent.com/open-goat/pequalnp-proofs/d780b209b4b8217b8da353e0b0782aef863dbcc2/lean/PEqualNP/Outside/L_meta_10036.lean -o /tmp/AffineLower.lean
(cd ../../lean && lake env python3 ../notes/affine-four-cover/assemble_exact.py /tmp/AffineLower.lean)
```
