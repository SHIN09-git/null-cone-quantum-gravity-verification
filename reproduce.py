"""Run either audit offline and preserve stdout, stderr and exit codes."""
import argparse
import hashlib
import json
import os
import platform
import subprocess
import sys
from importlib.metadata import version
from pathlib import Path

ROOT = Path(__file__).resolve().parent
PHASE1 = (
    ("symbolic", ["calculations/symbolic.py"], "symbolic.txt"),
    ("numerical", ["calculations/numerical.py"], "numerical.jsonl"),
    ("tests", ["tools/run_tests.py"], "tests.txt"),
    ("independent", ["tests/independent_checks.py"], "independent.txt"),
)
PHASE2 = (
    ("cut-algebra", ["phase2/calculations/algebra.py"], "cut-algebra.txt"),
    ("cut-numeric", ["phase2/calculations/experiments.py"], "cut-numeric.jsonl"),
    ("paired-check", ["phase2/calculations/independent.py"], "paired-check.txt"),
    ("recheck-algebra", ["phase2/calculations/exact_checks.py"], "recheck-algebra.txt"),
    ("recheck-numeric", ["phase2/calculations/numerical.py"], "recheck-numeric.jsonl"),
    ("tests", ["tools/run_tests.py", "--phase", "2"], "tests.txt"),
)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True, help="fresh directory outside this snapshot")
    parser.add_argument("--phase", type=int, choices=(1, 2), default=1, help="1: Section 4.4; 2: Section 5.2 and whole-paper recheck")
    parser.add_argument("--compare", action="store_true", help="also compare all output bytes to baseline/")
    args = parser.parse_args()
    out = args.out.resolve()
    if out.is_relative_to(ROOT) or out.exists():
        parser.error("choose a new output directory outside the snapshot")
    out.mkdir(parents=True)
    packages = {name: version(name) for name in ("sympy", "mpmath")}
    manifest = {"python": platform.python_version(), "packages": packages, "steps": []}
    if packages != {"sympy": "1.14.0", "mpmath": "1.3.0"}:
        parser.error("install the versions in requirements.txt")
    env = os.environ.copy()
    env.update(PYTHONIOENCODING="utf-8", PYTHONHASHSEED="0", PYTHONOPTIMIZE="0",
               PYTHONDONTWRITEBYTECODE="1", MPMATH_NOGMPY="1", SYMPY_GROUND_TYPES="python")
    success = True
    for name, arguments, stdout_file in (PHASE1 if args.phase == 1 else PHASE2):
        result = subprocess.run([sys.executable, "-B", "-u", *arguments], cwd=ROOT, env=env, capture_output=True)
        entry = {"command": ["python", "-B", "-u", *arguments], "exit_code": result.returncode, "sha256": {}}
        for filename, data in [(stdout_file, result.stdout), (name + ".stderr.txt", result.stderr)]:
            data = data.replace(b"\r\n", b"\n")
            (out / filename).write_bytes(data)
            entry["sha256"][filename] = digest(data)
        manifest["steps"].append(entry)
        print(name, "exit", result.returncode, flush=True)
        success &= result.returncode == 0
    path = out / "run.json"
    path.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8", newline="\n")
    if args.compare:
        baseline = ROOT / ("baseline" if args.phase == 1 else "phase2/baseline")
        actual = {f.name: f.read_bytes() for f in out.iterdir() if f.is_file()}
        reference = {f.name: f.read_bytes() for f in baseline.iterdir() if f.is_file()}
        differences = sorted(n for n in actual.keys() | reference.keys() if actual.get(n) != reference.get(n))
        if differences:
            print("Baseline byte differences:", ", ".join(differences))
            success = False
        else:
            print("All output files match the baseline byte for byte.")
    return 0 if success else 1


if __name__ == "__main__":
    raise SystemExit(main())
