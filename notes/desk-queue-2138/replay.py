"""Replay the exact finite searches captured by this desk audit."""
from collections import defaultdict
import argparse
import csv
from pathlib import Path
import re
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent


def rows(filename):
    with (HERE / filename).open(encoding="utf-8") as source:
        return list(csv.DictReader(source, delimiter="\t"))


def compile_program(compiler, directory, name, source):
    path = directory / f"{name}.cpp"
    path.write_text(source, encoding="utf-8")
    executable = directory / f"{name}.exe"
    subprocess.run([compiler, "-std=c++20", "-O3", str(path), "-o", str(executable)], check=True)
    return executable


def execute(command, *, inputs=None):
    result = subprocess.run(command, input=inputs, text=True, capture_output=True, check=True)
    return result.stdout + result.stderr


def replay_rectangles(compiler, directory):
    solver = compile_program(compiler, directory, "rectangular",
                             (HERE / "rectangular.cpp").read_text(encoding="utf-8"))
    groups = defaultdict(list)
    for row in rows("rectangular.tsv"):
        groups[row["rows"], row["cols"], row["budget"]].append(row)
    for (height, width, budget), cases in sorted(groups.items()):
        name = directory / f"{height}-{width}-{budget}.txt"
        name.write_text(f"{height} {width}\n" + "".join(
            f'{r["id"]} {r["mask"]} {r["cap"]}\n' for r in cases), encoding="utf-8")
        output = execute([str(solver), str(name), budget])
        expected = {(r["id"], r["visits"], r["result"]) for r in cases}
        observed = set(re.findall(r"^(L-meta-\d+) (\d+) (exhausted|timeout)$", output, re.M))
        if expected != observed:
            raise AssertionError(sorted(expected ^ observed))
        print(f"{height}×{width}, {budget} states per case: {len(cases)} checked", flush=True)


def replay_two_lit(compiler, directory, source, filename, monotone):
    if monotone:
        original = "const unsigned nots=cap+1-size;"
        if source.count(original) != 1:
            raise ValueError("Unexpected signed solver revision")
        source = source.replace(original, "const unsigned nots=0;")
    solver = compile_program(compiler, directory, "monotone" if monotone else "signed", source)
    cases = rows(filename)
    inputs = "".join(f'{r["id"]} {r["points"]} {r["mask"]} {r["cap"]}\n' for r in cases)
    output = execute([str(solver), "12000000"], inputs=inputs)
    expected = {(r["id"], r["visits"]) for r in cases}
    observed = set(re.findall(r"^(L-meta-\d+) UNSAT (\d+)$", output, re.M))
    if expected != observed:
        raise AssertionError(sorted(expected ^ observed))
    print(f"{filename}: {len(cases)} checked", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cxx", default="g++")
    parser.add_argument("--signed-source", type=Path)
    parser.add_argument("--skip-rectangles", action="store_true")
    args = parser.parse_args()
    with tempfile.TemporaryDirectory() as name:
        directory = Path(name)
        if not args.skip_rectangles:
            replay_rectangles(args.cxx, directory)
        if args.signed_source:
            source = args.signed_source.read_text(encoding="utf-8")
            replay_two_lit(args.cxx, directory, source, "signed.tsv", False)
            replay_two_lit(args.cxx, directory, source, "monotone-twolit.tsv", True)


if __name__ == "__main__":
    main()
