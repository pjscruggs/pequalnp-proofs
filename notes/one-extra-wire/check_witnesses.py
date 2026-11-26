"""Replay the explicit one-a-side circuits with no solver dependencies."""
OR, AND = False, True
two = [(OR,0,6),(OR,1,7),(OR,4,2),(OR,5,3),
       (OR,8,9),(AND,12,10),(AND,8,11),(OR,13,14)]
assigned = [(OR,0,1),(OR,6,7),(AND,9,10),(AND,0,8),(AND,2,5),
            (AND,3,4),(OR,11,12),(OR,13,14),(OR,15,16)]
# Embed the first two paths into a 6x6 graph, adjusting input and gate indices.
remap = [0,1,2,3,6,7,8,9] + list(range(12,20))
three = [(op,remap[a],remap[b]) for op,a,b in two] + [
    (OR,4,5),(AND,20,10),(AND,4,11),(OR,21,22),(OR,19,23)]


def check(n, m, target, gates):
    seen = 0
    for u in range(n):
        for v in range(m):
            wires = [i in (u,n+v) for i in range(n+m)]
            for op, a, b in gates:
                assert 0 <= a < len(wires) and 0 <= b < len(wires)
                wires.append(wires[a] and wires[b] if op == AND else wires[a] or wires[b])
            seen |= int(wires[-1]) << (m*u+v)
    assert seen == target
    print(f"{n}x{m} mask {target}: {len(gates)} gates, {n*m} cases passed")


if __name__ == "__main__":
    check(4, 4, 19475, two)
    check(6, 6, 17986273347, three)
    check(4, 5, 35228, assigned)
