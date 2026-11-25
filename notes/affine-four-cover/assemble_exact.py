"""Run in the pinned lake environment to check the exact affine covering number."""
from hashlib import sha256
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

EXPECTED = "d42060fbb9868ca85af75312844573c8198562476e825c4c32a82c57ef374a5c"
EXACT = """import AffineFourCover
import AffineLower

theorem affineFourExact : IsLeast {k | AffineFourCover.AtMost k} 11 :=
  AffineFourCover.least_of_lower PEqualNP.Outside.L_meta_10036

#print axioms affineFourExact
"""


def check(lower_path):
    lower = lower_path.read_text(encoding="utf-8-sig")
    if sha256(lower.encode()).hexdigest() != EXPECTED:
        raise ValueError("expected the lower proof from PR 18444, commit d780b20")
    with tempfile.TemporaryDirectory() as work:
        root = Path(work)
        env = dict(os.environ)
        search_path = [os.path.abspath(p) for p in env.get("LEAN_PATH", "").split(os.pathsep) if p]
        env["LEAN_PATH"] = os.pathsep.join([work, *search_path])
        shutil.copyfile(Path(__file__).with_name("AffineFourCover.lean"), root / "AffineFourCover.lean")
        # The pinned lower proof uses only declarations from its Mathlib imports.
        (root / "AffineLower.lean").write_text(lower.replace("import PEqualNP.Defs\n", "", 1), encoding="utf-8")
        (root / "AffineExact.lean").write_text(EXACT, encoding="utf-8")
        for module in ("AffineFourCover", "AffineLower", "AffineExact"):
            print(f"Checking {module}", flush=True)
            subprocess.run(["lean", "-o", module + ".olean", module + ".lean"],
                           cwd=root, env=env, check=True)


if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit("usage: lake env python3 assemble_exact.py LOWER.lean")
    check(Path(sys.argv[1]))
