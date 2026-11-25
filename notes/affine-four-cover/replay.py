"""Regenerate and independently check the five proofs of the eight-trace exclusion."""
import argparse
from pathlib import Path
import subprocess
import tempfile

from affine_extension_cnf import encode, orbits


def expect(command, code, marker):
    result = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    if result.returncode != code or marker not in result.stdout.splitlines():
        raise SystemExit(f"{command[0]} exited {result.returncode}\n{result.stdout}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--solver", default="cadical")
    parser.add_argument("--checker", default="lrat-trim")
    args = parser.parse_args()
    counts = []
    with tempfile.TemporaryDirectory() as work:
        cnf = Path(work) / "problem.cnf"
        proof = Path(work) / "proof.lrat"
        # At budget 15 the same generator allows all eleven affine traces.
        encode((), 15).write(cnf)
        expect([args.solver, "-q", "-n", cnf], 10, "s SATISFIABLE")
        print("15-rectangle positive control passed.", flush=True)
        for triple, size in orbits(3):
            encode(triple, 14).write(cnf)
            expect([args.solver, "-q", "-n", "--lrat", cnf, proof], 20, "s UNSATISFIABLE")
            expect([args.checker, cnf, proof], 20, "s VERIFIED")
            counts.append(size)
            print(f"Verified relaxed triple {triple}, orbit size {size}.", flush=True)
            proof.unlink()
    assert len(counts) == 5 and sum(counts) == 165
    print("All 165 choices verified.")
