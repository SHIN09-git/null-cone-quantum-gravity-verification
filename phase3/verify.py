"""Check versions, build the candidate and audit every public Lean theorem."""
import argparse
import json
import re
import shutil
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent
LEAN = "4.24.0"
LEAN_COMMIT = "797c613eb9b6d4ec95db23e3e00af9ac6657f24b"
MATHLIB = "f897ebcf72cd16f89ab4577d0c826cd14afaafc7"
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
PUBLIC = re.compile(r"^(?:@\[[^\n]*?\]\s*)?theorem\s+(\w+)", re.M)
UNTRUSTED = re.compile(r"\b(?:sorry|admit|sorryAx|axiom|unsafe|native_decide|run_cmd|run_tac|implemented_by|extern|skipKernelTC)\b")
AXIOM_LINE = re.compile(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)")
NAMESPACE = re.compile(r"^namespace (NullCone(?:\.\w+)+)$", re.M)


def sources():
    names = {}
    modules = []
    for path in sorted((ROOT / "NullCone").glob("*.lean")):
        source = path.read_text(encoding="utf-8")
        namespace = NAMESPACE.findall(source)
        if len(namespace) != 1:
            raise ValueError(f"Expected one project namespace in {path.name}")
        for name in PUBLIC.findall(source):
            full = namespace[0] + "." + name
            if full in names:
                raise ValueError(f"Duplicate public theorem {full}")
            names[full] = path
        modules.append("NullCone." + path.stem)
    for path in [*set(names.values()), ROOT / "NullCone.lean", ROOT / "Audit.lean"]:
        match = UNTRUSTED.search(path.read_text(encoding="utf-8"))
        if match:
            raise ValueError(f"Unexpected source token {match[0]} in {path.name}")
    audit = (ROOT / "Audit.lean").read_text(encoding="utf-8")
    commands = re.findall(r"^#print axioms (\S+)$", audit, re.M)
    if sorted(commands) != sorted(names):
        raise ValueError("Audit.lean theorem list differs from public declarations")
    index = (ROOT / "FORMALIZATION_MAP.md").read_text(encoding="utf-8")
    missing = sorted(n for n in names if f"`{n}`" not in index)
    if missing:
        raise ValueError(f"Missing theorem index entries {missing}")
    return names, modules


def run(argv, folder, filename):
    start = time.monotonic()
    with (folder / filename).open("wb") as log:
        result = subprocess.run(argv, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, check=False)
    seconds = round(time.monotonic() - start, 2)
    raw = (folder / filename).read_text(encoding="utf-8", errors="replace")
    print(f"{filename}  exit={result.returncode}  {seconds:.2f}s", flush=True)
    if result.returncode:
        raise RuntimeError(f"{filename} failed\n{raw[-3500:]}")
    return raw, seconds


def small(*args, cwd=ROOT):
    return subprocess.check_output(args, cwd=cwd, text=True, encoding="utf-8").strip()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--log-dir", type=Path, default=ROOT / ".lake" / "verification",
                        help="directory for complete combined output and the run record")
    parser.add_argument("--replay", type=Path, help="lean4checker executable built with the pinned Lean")
    args = parser.parse_args()
    out = args.log_dir.resolve()
    out.mkdir(parents=True, exist_ok=True)
    names, modules = sources()
    lake = shutil.which("lake")
    if not lake:
        raise RuntimeError("Install the pinned toolchain and put lake on PATH")
    if (ROOT / "lean-toolchain").read_text().strip() != "leanprover/lean4:v" + LEAN:
        raise RuntimeError("lean-toolchain pin changed")
    version = small(lake, "env", "lean", "--version")
    if f"version {LEAN}," not in version or LEAN_COMMIT[:12] not in version:
        raise RuntimeError("Unexpected Lean binary: " + version)
    deps = json.loads((ROOT / "lake-manifest.json").read_text())["packages"]
    pins = {p["name"]: p["rev"] for p in deps}
    if pins.get("mathlib") != MATHLIB:
        raise RuntimeError("Unexpected mathlib revision")
    for name, rev in pins.items():
        path = ROOT / ".lake" / "packages" / name
        if small("git", "rev-parse", "HEAD", cwd=path) != rev:
            raise RuntimeError(f"Dependency HEAD differs from pin for {name}")
        subprocess.run(["git", "diff", "--quiet", "HEAD", "--"], cwd=path, check=True)

    record = {"utc_start": datetime.now(timezone.utc).isoformat(), "lean": version,
              "lake": small(lake, "--version"), "dependencies": pins, "modules": modules,
              "counts": {"modules": len(modules), "public_theorems": len(names)}, "commands": []}
    def check(argv, filename):
        text, seconds = run(argv, out, filename)
        record["commands"].append({"argv": [Path(argv[0]).name, *[Path(s).name if Path(s).is_absolute() else s for s in argv[1:]]], "output": filename,
                                   "seconds": seconds, "exit": 0})
        return text
    build = check([lake, "build"], "build.log")
    if re.search(r"^warning: (?:NullCone[/\\]|Audit\.lean|NullCone\.lean)", build, re.M):
        raise RuntimeError("Project build contains a compiler warning")
    output = check([lake, "env", "lean", "-DwarningAsError=true", "Audit.lean"], "axioms.log")
    rows = {}
    for name, group in AXIOM_LINE.findall(output):
        listed = set(filter(None, (x.strip() for x in group.split(","))))
        if name in rows or listed - STANDARD:
            raise RuntimeError(f"Repeated theorem or nonstandard axiom for {name}: {listed}")
        rows[name] = sorted(listed)
    if rows.keys() != names.keys():
        raise RuntimeError(f"Audit output differs from the theorem list: {set(rows) ^ set(names)}")
    record["axioms_used"] = sorted(set().union(*rows.values()))
    probes = (ROOT / "review" / "Regression.lean").read_text(encoding="utf-8")
    if UNTRUSTED.search(probes):
        raise RuntimeError("Unexpected token in semantic regression checks")
    expected_probes = {"SemanticProbe." + n for n in PUBLIC.findall(probes)}
    tested = check([lake, "env", "lean", "-DwarningAsError=true", "review/Regression.lean"], "semantic-tests.log")
    actual_probes = {}
    for name, group in AXIOM_LINE.findall(tested):
        deps = set(filter(None, (x.strip() for x in group.split(","))))
        if deps - STANDARD or name in actual_probes:
            raise RuntimeError(f"Unexpected semantic audit result for {name}")
        actual_probes[name] = sorted(deps)
    if set(actual_probes) != expected_probes or not expected_probes:
        raise RuntimeError("Independent regression audit is incomplete")
    record["semantic_tests"] = sorted(actual_probes)
    record["replay"] = False
    if args.replay:
        checker = args.replay.resolve(strict=True)
        # One module at a time avoids loading many copies of mathlib into RAM.
        for module in modules:
            check([lake, "env", str(checker), "-v", module], "replay-" + module + ".log")
        record["replay"] = True
    record["utc_end"] = datetime.now(timezone.utc).isoformat()
    (out / "run.json").write_text(json.dumps(record, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(f"PASS  {len(modules)} proof modules, {len(rows)} public theorems; "
          f"observed axioms {', '.join(record['axioms_used'])}", flush=True)


if __name__ == "__main__":
    try:
        main()
    except (OSError, RuntimeError, ValueError, subprocess.CalledProcessError) as error:
        sys.exit(str(error))

