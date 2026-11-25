"""Benchmark actual one-rectangle completions of fixed thirteen-slot PG(2,4) states."""

import argparse
from collections import defaultdict
from itertools import combinations
from pathlib import Path
import random
import re
from statistics import median
import sys
from time import perf_counter

from trace_filter import TraceIndex


def mask(items):
    return sum(1 << i for i in items)


def points(value):
    while value:
        low = value & -value
        yield low.bit_length() - 1
        value ^= low


def load(note):
    sys.path.insert(0, str(note))
    import charts
    from affine_extension_cnf import SWARM_ROWS, POINT_LABEL, LINE_LABEL, SHAPES

    geom = note.parents[1] / "lean/PEqualNP/Outside/L_meta_9351.lean"
    original = [
        (mask(map(int, a.split(","))), mask(map(int, b.split(","))))
        for a, b in re.findall(
            r"\(\{([\d, ]+)\}, \{([\d, ]+)\}\)", geom.read_text(encoding="utf-8")
        )
    ]
    assert len(original) == 15
    whole = (1 << 21) - 1
    columns = [
        mask(i for i, r in enumerate(SWARM_ROWS) if r >> j & 1) for j in range(21)
    ]

    def closure(r):
        return mask(j for j, c in enumerate(columns) if not r & c)

    def footprint(r, c):
        return sum(c << (21 * i) for i in points(r))

    all_cells = sum((whole ^ r) << (21 * i) for i, r in enumerate(SWARM_ROWS))

    def decorate(r, c):
        assert c & ~closure(r) == 0
        return r, c, footprint(r, c)

    pool = {whole}
    for r in SWARM_ROWS:
        pool |= {c & ~r for c in pool}
    maximal = sorted(
        decorate(mask(i for i, r in enumerate(SWARM_ROWS) if not c & r), c)
        for c in pool
        if c != 0 and any(not r & c for r in SWARM_ROWS)
    )
    assert len(maximal) == 25235
    known = [decorate(r, c) for r, c in original]
    lifted = []
    for s in SHAPES:
        p = mask(POINT_LABEL[i] for i in points(s))
        lifted.append(decorate(p, closure(p)))
    words = [3, 5, 6, 9, 10]
    for b in range(4):
        r = mask(POINT_LABEL[d + 16] for d, w in enumerate(words) if w >> b & 1)
        lifted.append(decorate(r, closure(r)))

    def covered(seed):
        value = 0
        for _, _, foot in seed:
            value |= foot
        return value

    assert covered(known) == covered(lifted) == all_cells
    rowcharts = list(charts.charts())
    colcharts = [charts.dual_chart(item) for item in rowcharts]
    return rowcharts, colcharts, maximal, known, lifted, all_cells, covered


def scan(index, masks):
    for domain, families in index:
        traces = {m & domain for m in masks}
        if any(len(traces & f) >= 8 for f in families):
            return True
    return False


def grouped(charts):
    result = defaultdict(list)
    for chart in charts:
        result[chart.get("affine_points", chart.get("affine_lines"))].append(
            set(chart["traces"])
        )
    return list(result.items())


def timed(f, repeat=5):
    times = []
    for _ in range(repeat):
        start = perf_counter()
        answer = f()
        times.append(perf_counter() - start)
    return answer, median(times)


def run(note):
    start = perf_counter()
    rc, cc, pool, known, lifted, all_cells, covered = load(note)
    print("Loaded pool, seeds and charts", round(perf_counter() - start, 3), flush=True)
    start = perf_counter()
    row, col = TraceIndex(rc), TraceIndex(cc)
    base = grouped(rc), grouped(cc)
    print(
        "Two indexes",
        round(perf_counter() - start, 3),
        "seconds;",
        len(row.traces),
        "distinct (domain,trace) pairs per side",
        flush=True,
    )
    rng = random.Random(9348)

    def drops(seed):
        return [
            [slot for d, slot in enumerate(seed) if d not in pair]
            for pair in combinations(range(15), 2)
        ]

    # A boundary cohort fixes seven affine rectangles and six independently
    # sampled maximal projective rectangles per prefix.
    boundary = [rng.sample(lifted[:11], 7) + rng.sample(pool, 6) for _ in range(105)]
    names = ("published-15", "affine-15", "affine-seven", "random")
    groups = [
        drops(known),
        drops(lifted),
        boundary,
        [rng.sample(pool, 13) for _ in range(105)],
    ]
    # Exercise push/pop including a duplicate rectangle and duplicate affine
    # traces from different masks. Compare every step with a fresh direct scan.
    for index, ref, side in ((row, base[0], 0), (col, base[1], 1)):
        state = index.state()
        dom, families = ref[0]
        traces = sorted(families[0])[:7]
        outside = ((1 << 21) - 1) ^ dom
        candidates = traces + [
            traces[0],
            traces[0] | (outside & -outside),
            sorted(families[0])[7],
            lifted[0][side],
        ]
        for m in candidates:
            assert state.rejects_next(m) == scan(ref, [*state.stack, m])
            state.push(m)
            assert bool(state.violations) == scan(ref, state.stack)
        while state.stack:
            state.pop()
            assert bool(state.violations) == scan(ref, state.stack)
    for name, prefixes in zip(names, groups):
        # Decision variant: one rectangle covers exactly the remaining pairs
        # iff the union of their line sets avoids every remaining point.
        from affine_extension_cnf import SWARM_ROWS

        def last_slot_decision():
            solutions = 0
            for pre in prefixes:
                missing = all_cells ^ covered(pre)
                pos, forbidden = 0, 0
                for row in SWARM_ROWS:
                    lines = missing & ((1 << 21) - 1)
                    missing >>= 21
                    if lines:
                        pos |= lines
                        forbidden |= row
                solutions += not (pos & forbidden)
            return solutions

        def ref_test():
            status = []
            for j, pre in enumerate(prefixes):
                rows = [t[0] for t in pre]
                cols = [t[1] for t in pre]
                for candidate in pool[(j * 19) % 1000 :: 3503]:
                    status.append(
                        scan(base[0], [*rows, candidate[0]])
                        or scan(base[1], [*cols, candidate[1]])
                    )
            return status

        def index_test(validate_compiled=False):
            status = []
            for j, pre in enumerate(prefixes):
                a = row.state(t[0] for t in pre)
                b = col.state(t[1] for t in pre)
                aa, bb = (
                    (a.rejected_masks(), b.rejected_masks())
                    if validate_compiled
                    else (None, None)
                )
                for candidate in pool[(j * 19) % 1000 :: 3503]:
                    status.append(
                        a.rejects_next(candidate[0]) or b.rejects_next(candidate[1])
                    )
                    if validate_compiled:
                        assert status[-1] == (
                            aa is None
                            or bb is None
                            or candidate[0] in aa
                            or candidate[1] in bb
                        )
            return status

        truth, scan_time = timed(ref_test, 3)
        indexed, index_time = timed(index_test, 3)
        assert indexed == truth == index_test(True)

        def complete(filtering):
            pruned, good, whole_prefixes = 0, 0, 0
            for pre in prefixes:
                missing = all_cells ^ covered(pre)
                if not filtering:
                    good += sum(1 for _, _, foot in pool if missing & foot == missing)
                    continue
                a = row.state(t[0] for t in pre).rejected_masks()
                b = col.state(t[1] for t in pre).rejected_masks()
                if a is None or b is None:
                    pruned += len(pool)
                    whole_prefixes += 1
                    continue
                if not a and not b:
                    good += sum(1 for _, _, foot in pool if missing & foot == missing)
                    continue
                for r, c, foot in pool:
                    if r in a or c in b:
                        pruned += 1
                    elif missing & foot == missing:
                        good += 1
            return good, pruned, whole_prefixes

        actual, bt = timed(lambda: complete(False), 3)
        out, ft = timed(lambda: complete(True), 3)
        decisions, dt = timed(last_slot_decision, 5)
        assert actual[0] == out[0] and bool(actual[0]) == bool(decisions)
        print(
            name,
            "candidates",
            len(prefixes) * len(pool),
            "pruned",
            out[1],
            "prefixes",
            out[2],
            "valid",
            out[0],
            "baseline_s",
            round(bt, 4),
            "filtered_s",
            round(ft, 4),
            "sample_checks",
            len(truth),
            "chart_scan_s",
            round(scan_time, 4),
            "inverted_query_s",
            round(index_time, 4),
            "decision_only_s",
            round(dt, 6),
            flush=True,
        )


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "notes_directory", type=Path, nargs="?", default=Path(__file__).resolve().parent
    )
    run(parser.parse_args().notes_directory.resolve())
