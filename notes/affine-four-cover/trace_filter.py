"""Incremental overlap filter for point- or line-side constraints from charts.py.

Pass a single side's exported JSON objects to TraceIndex. Push and pop masks
as rectangle sets become fixed. A partial state with eight distinct traces
from one chart cannot extend to a cover using at most fourteen rectangles.
"""

from collections import defaultdict


class TraceIndex:
    def __init__(self, charts):
        groups = defaultdict(list)
        source_side = None
        for chart in charts:
            sides = [k for k in ("affine_points", "affine_lines") if k in chart]
            if len(sides) != 1 or (source_side is not None and source_side != sides[0]):
                raise ValueError("supply all row charts or all column charts")
            source_side = sides[0]
            domain = chart[source_side]
            traces = chart["traces"]
            if (
                not 0 <= domain < 1 << 21
                or domain.bit_count() != 16
                or chart["max_matches"] != 7
                or len(set(traces)) != 11
                or any(t < 0 or t & ~domain for t in traces)
            ):
                raise ValueError("expected a PG(2,4) chart on one side")
            groups[domain].append(traces)
        if not groups:
            raise ValueError("missing charts")
        self.traces = []
        self.extensions = []
        self.postings = defaultdict(list)
        self.domain_count = len(groups)
        for d, (domain, families) in enumerate(groups.items()):
            by_trace = defaultdict(int)
            for i, family in enumerate(families):
                for trace in family:
                    by_trace[trace] |= 1 << i
            outside = ((1 << 21) - 1) ^ domain
            for trace, family_bits in by_trace.items():
                ident = len(self.traces)
                self.traces.append((d, family_bits))
                self.extensions.append((trace, outside))
                sub = outside
                while True:
                    self.postings[trace | sub].append(ident)
                    if sub == 0:
                        break
                    sub = (sub - 1) & outside

    def state(self, masks=()):
        return TraceState(self, masks)


class TraceState:
    def __init__(self, index, masks):
        self.index = index
        self.counts = [0] * len(index.traces)
        self.bits = [[0] * 4 for _ in range(index.domain_count)]
        self.violations = 0
        self.stack = []
        for mask in masks:
            self.push(mask)

    def _change(self, mask, delta):
        for ident in self.index.postings.get(mask, ()):
            self.counts[ident] += delta
            if self.counts[ident] != (1 if delta == 1 else 0):
                continue
            domain, families = self.index.traces[ident]
            bits = self.bits[domain]
            before = bits[3].bit_count()
            carry = families
            for j in range(4):
                old = bits[j]
                bits[j] ^= carry
                carry &= old if delta == 1 else ~old
                if not carry:
                    break
            self.violations += bits[3].bit_count() - before

    def push(self, mask):
        if len(self.stack) >= 14:
            raise ValueError(
                "this exclusion applies only to covers of at most 14 rectangles"
            )
        if not 0 <= mask < (1 << 21):
            raise ValueError("rectangle mask outside the 21-point ground set")
        self._change(mask, 1)
        self.stack.append(mask)

    def pop(self):
        mask = self.stack.pop()
        self._change(mask, -1)
        return mask

    def rejects_next(self, mask):
        if len(self.stack) >= 14 or not 0 <= mask < (1 << 21):
            raise ValueError(
                "expected a legal mask and a prefix with fewer than 14 fixed slots"
            )
        if self.violations:
            return True
        for ident in self.index.postings.get(mask, ()):
            if self.counts[ident]:
                continue
            domain, families = self.index.traces[ident]
            a, b, c, _ = self.bits[domain]
            if families & a & b & c:
                return True
        return False

    def rejected_masks(self):
        """Return all banned next masks, or None when this entire prefix is banned."""
        if len(self.stack) >= 14:
            raise ValueError("no open slots in the 14-cover")
        if self.violations:
            return None
        near = [a & b & c for a, b, c, _ in self.bits]
        rejected = set()
        if not any(near):
            return rejected
        for ident, (domain, families) in enumerate(self.index.traces):
            if self.counts[ident] or not near[domain] & families:
                continue
            trace, outside = self.index.extensions[ident]
            sub = outside
            while True:
                rejected.add(trace | sub)
                if sub == 0:
                    break
                sub = (sub - 1) & outside
        return rejected
