"""Optional online check of the upstream bytes. Does not store the manuscript."""
import hashlib
import json
from pathlib import Path
from urllib.request import Request, urlopen


def main():
    record = Path(__file__).resolve().parents[1] / "reference" / "paper.json"
    for entry in json.loads(record.read_text(encoding="utf-8"))["files"]:
        digest = hashlib.sha256()
        length = 0
        request = Request(entry["url"], headers={"Accept-Encoding": "identity", "User-Agent": "null-cone-section-audit/0.1.0"})
        with urlopen(request, timeout=60) as response:
            while chunk := response.read(65536):
                digest.update(chunk)
                length += len(chunk)
        print(entry["url"], length, digest.hexdigest())
        if (length, digest.hexdigest()) != (entry["bytes"], entry["sha256"]):
            raise SystemExit("Upstream response differs from the recorded bytes.")
    print("PASS")


if __name__ == "__main__":
    main()
