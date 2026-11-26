"""Check the rectangle cover and integer edge weights against the Lean table."""

import json
import re
import sys
from pathlib import Path


def verify(lean_path, certificate_path):
    text = lean_path.read_text(encoding="utf-8-sig")
    match = re.search(r"\[\s*(0x[0-9a-fA-F]+(?:\s*,\s*0x[0-9a-fA-F]+){31})\s*\]\s*:\s*List", text)
    if not match:
        raise ValueError("Expected 32 hexadecimal rows in the Lean statement")
    rows = [int(token, 16) for token in match[1].split(",")]
    size = len(rows)
    full = (1 << size) - 1
    assert all(0 <= row <= full for row in rows)

    data = json.loads(certificate_path.read_text(encoding="utf-8"))
    rectangles = [(int(r, 16), int(c, 16)) for r, c in data["cover"]]
    covered = [0] * size
    for row_set, col_set in rectangles:
        assert 0 < row_set <= full and 0 < col_set <= full
        for i in range(size):
            if row_set >> i & 1:
                covered[i] |= col_set
    assert covered == rows, "The rectangle union differs from the posted table"

    weights = data["row_weights"]
    assert len(weights) == size
    for i, row_weights in enumerate(weights):
        assert len({j for j, _ in row_weights}) == len(row_weights)
        for j, weight in row_weights:
            assert type(j) is int and 0 <= j < size and rows[i] >> j & 1
            assert type(weight) is int and weight > 0
    total = sum(weight for row in weights for _, weight in row)

    # A maximal rectangle's column set is the intersection of its rows.
    intersections = {full}
    for row in rows:
        intersections |= {cols & row for cols in intersections}
    loads = []
    for cols in intersections - {0}:
        containing = [i for i, row in enumerate(rows) if row & cols == cols]
        if containing:
            loads.append(sum(weight for i in containing for j, weight in weights[i] if cols >> j & 1))
    maximum = max(loads)
    floor = (total + maximum - 1) // maximum
    print(f"{sum(row.bit_count() for row in rows)} edges covered by {len(rectangles)} rectangles")
    print(f"{len(loads)} maximal rectangles, maximum weight {maximum}, total weight {total}")
    print(f"Minimum rectangle count lies between {floor} and {len(rectangles)}")


if __name__ == "__main__":
    directory = Path(__file__).resolve().parent
    lean = Path(sys.argv[1]) if len(sys.argv) > 1 else directory / "Keyed32Upper.lean"
    certificate = Path(sys.argv[2]) if len(sys.argv) > 2 else directory / "rectangle_certificate.json"
    verify(lean, certificate)
