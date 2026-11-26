"""Compile the English report in an isolated directory. Requires pdfLaTeX."""
import argparse
from datetime import datetime, timezone
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--phase", type=int, choices=(1, 2), default=1)
    parser.add_argument("--out", type=Path, required=True, help="a new PDF filename")
    parser.add_argument("--logs", type=Path, help="optional new directory for raw local TeX logs")
    args = parser.parse_args()
    out = args.out.resolve()
    if out.exists():
        parser.error("output file already exists")
    if args.logs:
        args.logs.mkdir(parents=True, exist_ok=False)
    env = os.environ.copy()
    epoch = datetime(2026, 11, 26, tzinfo=timezone.utc).timestamp()
    env.update(SOURCE_DATE_EPOCH=str(int(epoch)), FORCE_SOURCE_DATE="1", TZ="UTC")
    command = ["pdflatex", "-no-shell-escape", "-halt-on-error", "-interaction=nonstopmode", "report.tex"]
    with tempfile.TemporaryDirectory() as directory:
        work = Path(directory)
        source_directory = ROOT / ("report" if args.phase == 1 else "phase2/report")
        for source in source_directory.glob("*.tex"):
            shutil.copyfile(source, work / source.name)
        for index in (1, 2):
            result = subprocess.run(command, cwd=work, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            if args.logs:
                (args.logs / f"pass-{index}.txt").write_bytes(result.stdout)
                if (work / "report.log").is_file():
                    shutil.copyfile(work / "report.log", args.logs / f"pass-{index}.log")
            if result.returncode:
                raise SystemExit(result.stdout.decode(errors="replace")[-3500:])
        out.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(work / "report.pdf", out)
    print(out.name)


if __name__ == "__main__":
    main()
