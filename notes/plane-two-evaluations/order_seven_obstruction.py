"""Verify a two-term PG(2,7) minor missed by both proposed assignments."""

labels = [(1, x, y) for x in range(7) for y in range(7)]
labels += [(0, 1, y) for y in range(7)] + [(0, 0, 1)]
rows = [0, 1, 7, 8, 14, 16, 52, 35, 24, 31, 40, 21, 37, 54]
cols = [49, 48, 42, 24, 21, 9, 29, 33, 2, 10, 16, 19, 11, 53]
assert len(set(rows)) == len(set(cols)) == len(rows) == 14

for k, line in enumerate(cols):
    incident = [i for i in rows if sum(a*b for a,b in zip(labels[i], labels[line])) % 7 == 0]
    assert set(incident) == {rows[k], rows[(k+1) % len(rows)]}

def exponents(i, j):
    x = 1 + 57*i + j
    return pow(x, 4, 8179), pow(x+305, 3, 8179)

for k, expected in enumerate((6510, 530)):
    first = sum(exponents(i, j)[k] for i, j in zip(rows, cols)) % 8191
    second = sum(exponents(i, j)[k] for i, j in zip(rows[1:]+rows[:1], cols)) % 8191
    assert first == second == expected
    print(f"Assignment {k+1}: both alternating exponents are {first}.")
