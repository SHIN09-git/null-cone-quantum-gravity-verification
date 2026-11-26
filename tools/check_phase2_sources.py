"""Verify the two versioned arXiv sources and the lines cited in the closure audit."""
import argparse
from hashlib import sha256
import io
import json
from pathlib import Path
import re
import tarfile
from urllib.request import Request, urlopen

ROOT = Path(__file__).resolve().parents[1]


def source_bytes(entry, directory):
    if directory:
        data = (directory / entry["name"]).read_bytes()
    else:
        request = Request(entry["url"], headers={"Accept-Encoding":"identity",
                          "User-Agent":"null-cone-gravity-verification/0.2.0"})
        with urlopen(request, timeout=60) as response:
            data = response.read(entry["bytes"]+1)
    if len(data) != entry["bytes"] or sha256(data).hexdigest() != entry["sha256"]:
        raise SystemExit("Version fingerprint mismatch: " + entry["name"])
    print(entry["name"], len(data), entry["sha256"])
    return data


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-dir", type=Path, help="read all three named files from a directory instead of arXiv")
    parser.add_argument("--pdf-pages", action="store_true", help="also inspect PDF destinations (requires PyMuPDF)")
    parser.add_argument("--outline", action="store_true", help="also compare the frozen HTML equation index (requires lxml and PyMuPDF)")
    args = parser.parse_args()
    record = json.loads((ROOT/"reference/phase2.json").read_text(encoding="utf-8"))
    files = {item["name"]:source_bytes(item,args.source_dir) for item in record["files"]}
    with tarfile.open(fileobj=io.BytesIO(files["source-v1.tar.gz"]), mode="r:gz") as archive:
        with archive.extractfile(record["tex_member"]) as member:
            tex = member.read()
    if sha256(tex).hexdigest() != record["tex_sha256"]:
        raise SystemExit("TeX member mismatch")
    lines = tex.decode("utf-8").splitlines()
    for number, expected in record["tex_line_sha256"].items():
        if sha256(lines[int(number)-1].encode("utf-8")).hexdigest() != expected:
            raise SystemExit("TeX line mismatch: " + number)
    print("TeX source lines:", ", ".join(record["tex_line_sha256"]))
    if args.pdf_pages or args.outline:
        import pymupdf
        with pymupdf.open(stream=files["paper-v1.pdf"], filetype="pdf") as paper:
            names = paper.resolve_names()
            for tag, page in record["equation_pdf_pages"].items():
                if names["equation."+tag]["page"]+1 != page:
                    raise SystemExit("PDF locator mismatch: " + tag)
        with pymupdf.open(stream=files["2310.02189v3.pdf"], filetype="pdf") as ref:
            excerpt = " ".join(ref[record["ref36_axiom_1"]["pdf_page"]-1].get_text().split())
            if "Axiom 1. Finiteness:" not in excerpt:
                raise SystemExit("Could not locate Axiom 1 in reference [36].")
        print(len(record["equation_pdf_pages"]),"PDF equation destinations and reference [36] checked")
    if args.outline:
        from lxml import html
        page = html.fromstring(source_bytes(record["html_snapshot"],args.source_dir),
                               parser=html.HTMLParser(encoding="utf-8"))
        eq_nodes = page.xpath('//*[contains(concat(" ",normalize-space(@class)," ")," ltx_tag_equation ")]')
        html_tags = {node.text_content().strip("() ") for node in eq_nodes}
        pdf_tags = {k.removeprefix("equation.") for k in names if k.startswith("equation.")}
        extra = pdf_tags-html_tags
        single = {k for k in extra if not any(re.fullmatch(re.escape(k)+r"[a-z]",h) for h in html_tags)}
        head = re.compile(r"^\\(?:section|subsection)\*?(?:\[[^\]]*\])?\{.+\}\s*$")
        headings = sum(bool(head.match(re.split(r"(?<!\\)%",line,maxsplit=1)[0])) for line in lines)
        refs = sum(k.startswith("cite.") for k in names)
        if not (headings == 45 and refs == 84 and len(html_tags) == len(eq_nodes) == 526
                and html_tags <= pdf_tags and len(extra) == 82 and single == {"A.14","A.32","C.21","D.4"}):
            raise SystemExit("Full-paper outline differs from the recorded index.")
        print(headings,"outline entries,",refs,"PDF references,",len(html_tags),"HTML tags; extra single equations",sorted(single))
    print("PASS")


if __name__ == "__main__":
    main()
