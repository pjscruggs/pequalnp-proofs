"""Check the generated six-input transfers inside the repository's lake environment."""

import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

from instantiate import generate

HERE = Path(__file__).resolve().parent
EXAMPLES = json.loads((HERE / "examples.json").read_bytes())
KINDS = [
    ("OutputOr", 0xFEEEFAEAFEAAEAAA),
    ("OutputAnd", 0xA888A080A8008000),
    ("InputAnd", 0xEAC8E080C0C0C000),
    ("InputOr", 0xFFCCF0C0EAC8E080),
    ("Unused", 0xEAC8E080EAC8E080),
]


def verify(all_rows):
    examples = [(name, 0xEAC8E080, child, 8664) for name, child in KINDS]
    if all_rows:
        examples.extend(
            (f"Gap{cid}", int(parent, 0), int(child, 0), pid)
            for cid, child, pid, parent in EXAMPLES
        )
    with tempfile.TemporaryDirectory() as temp:
        root = Path(temp)
        env = dict(os.environ)
        paths = [
            str(Path(p).resolve())
            for p in env.get("LEAN_PATH", "").split(os.pathsep)
            if p
        ]
        env["LEAN_PATH"] = os.pathsep.join([temp, *paths])
        for mod in ["CofactorTransfer", "InputPair", "TableTransfer", "NineGates"]:
            shutil.copyfile(HERE / (mod + ".lean"), root / (mod + ".lean"))
            subprocess.run(
                ["lean", "-o", mod + ".olean", mod + ".lean"],
                cwd=root,
                env=env,
                check=True,
            )
        (root / "Audit.lean").write_text(
            "import TableTransfer\nimport NineGates\n"
            "#print axioms CofactorTransfer.padInherits\n#print axioms NineGates.lower\n"
            "#print axioms NineGates.upper\n",
            encoding="utf-8",
        )
        subprocess.run(["lean", "Audit.lean"], cwd=root, env=env, check=True)
        for name, parent, child, pid in examples:
            target = root / (name + ".lean")
            target.write_text(generate(parent, child, pid), encoding="utf-8")
            result = subprocess.run(
                ["lean", str(target)],
                cwd=root,
                env=env,
                check=True,
                stdout=subprocess.PIPE,
                text=True,
            )
            if (
                "[propext, Classical.choice, Quot.sound]" not in result.stdout
                or "sorryAx" in result.stdout
            ):
                raise RuntimeError(result.stdout)
            print(f"{name}: verified via L-meta-{pid}", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--all", action="store_true", help="also replay the 21 published row mappings"
    )
    parser.add_argument(
        "--modules", action="store_true", help="list required lake build targets"
    )
    args = parser.parse_args()
    if args.modules:
        parents = sorted({8664} | ({row[2] for row in EXAMPLES} if args.all else set()))
        print(
            " ".join(
                [
                    "PEqualNP.MetaComplexity.Helpers.ForestElim",
                    "PEqualNP.Defs.MetaComplexityLgpMono",
                    *(f"PEqualNP.Outside.L_meta_{p}" for p in parents),
                ]
            )
        )
    else:
        verify(args.all)
