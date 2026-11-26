"""Check the member hashes or build the deterministic distribution from verified members."""
import argparse
from hashlib import sha256
from pathlib import Path
from zipfile import ZIP_STORED, ZipFile, ZipInfo

ROOT = Path(__file__).resolve().parents[1]
PREFIX = "null-cone-4.4-v0.1.0"
MANIFEST = "SHA256SUMS"


def members():
    expected = {}
    for line in (ROOT / MANIFEST).read_text(encoding="ascii").splitlines():
        checksum, separator, name = line.partition("  ")
        if not separator or name in expected or len(checksum) != 64:
            raise ValueError("invalid or repeated manifest entry")
        expected[name] = checksum
    actual = set()
    for entry in ROOT.iterdir():
        if entry.name == ".git":
            continue  # A checkout can use either a metadata directory or a worktree pointer.
        paths = entry.rglob("*") if entry.is_dir() else (entry,)
        actual.update(p.relative_to(ROOT).as_posix() for p in paths if p.is_file())
    if actual != set(expected) | {MANIFEST}:
        raise SystemExit("member list mismatch: " + ", ".join(sorted(actual ^ (set(expected) | {MANIFEST}))))
    for name, checksum in expected.items():
        if sha256((ROOT / name).read_bytes()).hexdigest() != checksum:
            raise SystemExit("member checksum mismatch: " + name)
    print(f"PASS: {len(expected)} member hashes; exact file list.")
    return sorted(actual)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--zip", type=Path, help="write a new archive outside the extracted tree")
    args = parser.parse_args()
    names = members()
    if args.zip:
        target = args.zip.resolve()
        if target.is_relative_to(ROOT):
            parser.error("choose an archive location outside the tree")
        with ZipFile(target, mode="x", compression=ZIP_STORED) as archive:
            for name in names:
                info = ZipInfo(PREFIX + "/" + name, (2026, 11, 26, 0, 0, 0))
                info.create_system = 3
                info.external_attr = 0o100644 << 16
                info.compress_type = ZIP_STORED
                archive.writestr(info, (ROOT / name).read_bytes())
        print(sha256(target.read_bytes()).hexdigest(), target.name)


if __name__ == "__main__":
    main()
