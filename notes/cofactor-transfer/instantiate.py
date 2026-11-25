"""Generate a Lean transfer from a 32-bit parent table to a 64-bit child table."""

import argparse
from itertools import permutations


def transform(parent, rule, variable):
    table = 0
    for word in range(64):
        old, fresh = word & 31, word >> 5
        if rule == "input AND" and not fresh:
            old &= ~(1 << variable)
        if rule == "input OR" and fresh:
            old |= 1 << variable
        value = parent >> old & 1
        if rule == "output AND":
            value &= fresh
        if rule == "output OR":
            value |= fresh
        table |= value << word
    return table


def matching_rule(parent, child):
    rules = [("unused", None)]
    if parent not in (0, 2**32 - 1):
        rules += [("output AND", None), ("output OR", None)]
    for i in range(5):
        if any((parent >> x ^ parent >> (x ^ (1 << i))) & 1 for x in range(32)):
            rules.extend((kind, i) for kind in ("input AND", "input OR"))
    options = {}
    for rule, variable in rules:
        options.setdefault(transform(parent, rule, variable), (rule, variable))
    for p in permutations(range(6)):
        # Normalized input i is supplied by child wire p[i].
        inverse_words = [
            sum((w >> i & 1) << j for i, j in enumerate(p)) for w in range(64)
        ]
        normalized = sum((child >> w & 1) << i for i, w in enumerate(inverse_words))
        if normalized in options:
            rule, variable = options[normalized]
            return rule, variable, p
    raise ValueError(
        "no unused-input, output-padding or essential-input-pair reduction matches"
    )


def vector(values):
    return "![" + ", ".join(map(str, values)) + "]"


def point(word):
    return f"(fun i : Fin 5 => Nat.testBit {word} i.val)"


def generate(parent, child, parent_gap=None):
    if not 0 <= parent < 2**32 or not 0 <= child < 2**64:
        raise ValueError("expected an unsigned 32-bit parent and unsigned 64-bit child")
    rule, v, p = matching_rule(parent, child)
    imports = ["import TableTransfer"]
    if parent_gap is not None:
        imports.append(f"import PEqualNP.Outside.L_meta_{parent_gap}")
    lines = [
        *imports,
        "",
        "namespace GeneratedTransfer",
        "open CofactorTransfer",
        "",
        "def tab {n : ℕ} (bits : ℕ) (x : Fin n → Bool) : Bool :=",
        "  bits.testBit (∑ i : Fin n, if x i then 2 ^ i.val else 0)",
        "",
        f"def parentFn : (Fin 5 → Bool) → Bool := tab {parent:#x}",
        f"def childFn : (Fin 6 → Bool) → Bool := tab {child:#x}",
        "",
        "theorem transfer (parent : NoSaving parentFn) : NoSaving childFn := by",
        "  let π : Equiv.Perm (Fin 6) :=",
        f"    ⟨{vector(p)}, {vector([p.index(i) for i in range(6)])}, by decide +kernel, by decide +kernel⟩",
    ]
    a = str(rule.endswith("AND")).lower()
    if rule == "unused":
        fn = "fun x : Fin 6 → Bool => parentFn (x ∘ Fin.castSucc)"
        proof = "unusedInherits parentFn parent"
    elif rule.startswith("output"):
        op = "&&" if a == "true" else "||"
        fn = f"fun x : Fin 6 → Bool => x (Fin.last 5) {op} parentFn (fun i => x i.castSucc)"
        u = next(i for i in range(32) if not (parent >> i & 1))
        w = next(i for i in range(32) if parent >> i & 1)
        proof = f"padInherits parentFn ⟨{point(u)}, {point(w)}, by decide +kernel⟩ {a} parent"
    else:
        fn = f"fun x : Fin 6 → Bool => parentFn (splitInputs {v} {a} x)"
        w = next(i for i in range(32) if (parent >> i ^ parent >> (i ^ (1 << v))) & 1)
        proof = f"pairInherits parentFn {v} ⟨{point(w)}, by decide +kernel⟩ {a} parent"
    lines += [
        f"  let normalized := {fn}",
        f"  have base : NoSaving normalized := {proof}",
        "  have same : childFn = fun x => normalized (x ∘ π) := funext (by decide +kernel)",
        "  rw [same]",
        "  exact renamedInherits π normalized base",
    ]
    if parent_gap is not None:
        lines += [
            "",
            "theorem child : NoSaving childFn :=",
            f"  transfer PEqualNP.Outside.L_meta_{parent_gap}",
            "",
            "#print axioms child",
        ]
    lines += ["", "end GeneratedTransfer", ""]
    return "\n".join(lines)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("parent", type=lambda s: int(s, 0))
    parser.add_argument("child", type=lambda s: int(s, 0))
    parser.add_argument(
        "--parent-gap", type=int, help="instantiate with a merged L-meta theorem"
    )
    args = parser.parse_args()
    try:
        print(generate(args.parent, args.child, args.parent_gap), end="")
    except ValueError as err:
        parser.error(str(err))
