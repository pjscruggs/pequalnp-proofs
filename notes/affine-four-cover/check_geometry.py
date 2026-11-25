"""Reconstruct the order-four plane and cover from a one-factorization of K6."""
from itertools import combinations
from affine_extension_cnf import SHAPES

ROWS = (69905, 74274, 83012, 100488, 164897, 149522, 139652, 135752,
        272449, 267394, 295444, 278824, 541313, 557378, 530468, 533528)
CENTER = 4
# The edge labels of the fifteen noncentral points, in desk order.
LABELS = ("15", "02", "12", "05", "", "34", "25", "01",
          "04", "03", "13", "14", "23", "24", "35", "45")
MATCHINGS = ("01 25 34", "04 15 23", "05 13 24", "02 14 35", "03 12 45")


def check():
    edges = {edge: i for i, edge in enumerate(LABELS) if edge}
    if set(edges) != {"".join(e) for e in combinations("012345", 2)}:
        raise ValueError("point labels must exhaust the edges of K6")
    plane_lines, row_sets = set(), []
    for matching in MATCHINGS:
        pairs = matching.split()
        ray = frozenset(edges[e] for e in pairs)
        row_sets.append(ray)
        plane_lines.add(ray | {CENTER})
        for a, b in combinations(pairs, 2):
            plane_lines.add(frozenset(edges["".join(sorted((u, v)))] for u in a for v in b))
    columns = [frozenset(i for i, row in enumerate(ROWS) if row >> j & 1) for j in range(20)]
    if len(plane_lines) != 20 or plane_lines != set(columns):
        raise ValueError("constructed lines differ from the desk matrix")
    for vertex in "012345":
        row_sets.append({CENTER} | {i for edge, i in edges.items() if vertex in edge})
    covered = set()
    # Images of our points and lines in the coordinate system of the merged witness.
    point_map = (0,5,10,15,13,8,7,2,6,3,12,9,11,14,1,4)
    line_map = (8,11,9,10,0,1,2,3,12,14,15,13,16,17,18,19,4,6,7,5)
    published = {(41068,266785),(13829,141352),(27808,74881),(14602,136212),
                 (546,557389),(25424,82456),(388,557490),(1048,553282),
                 (53248,491842),(41107,280708),(2113,560706)}
    assert sorted(point_map) == list(range(16)) and sorted(line_map) == list(range(20))
    assert all((row >> j & 1) == (ROWS[point_map[i]] >> line_map[j] & 1)
               for i, row in enumerate(ROWS) for j in range(20))
    assert {sum(1 << p for p in points) for points in row_sets} == set(SHAPES)
    remapped = set()
    for points in row_sets:
        lines = [j for j, line in enumerate(columns) if points.isdisjoint(line)]
        remapped.add((sum(1 << point_map[i] for i in points), sum(1 << line_map[j] for j in lines)))
        covered.update((i, j) for i in points for j in lines)
    assert remapped == published
    zeros = {(i, j) for i, row in enumerate(ROWS) for j in range(20) if not (row >> j & 1)}
    if covered != zeros or len(row_sets) != 11:
        raise ValueError("rectangle verification failed")
    print(f"Reconstructed {len(plane_lines)} lines. All {len(zeros)} zeros covered by 11 rectangles.")


if __name__ == "__main__":
    check()
