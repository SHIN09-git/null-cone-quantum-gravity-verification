# Reproduce the Section 5.2 audit

The six calculations run offline with the same two pinned dependencies as the Section 4.4 release. From the repository root, use CPython 3.12.10 and a fresh output directory outside the checkout. Choose the Python executable from the virtual environment used to install the dependencies.

~~~sh
python -m pip install --only-binary=:all: --require-hashes -r requirements.txt
python -B tools/snapshot.py
python -B reproduce.py --phase 2 --out ../null-cone-phase2-run --compare
~~~

The runner records the command, exit code, stdout, stderr, output hashes, Python version and library versions. It normalizes output line endings to LF. The comparison checks all 13 files in [the public baseline](baseline/), including the environment manifest. Byte comparisons may differ on other Python versions or math libraries. Running without the comparison switch retains the scientific assertions. Section 4.4 has its own public baseline and 11 tests. [Public run manifest](baseline/run.json) · [Earlier release](https://github.com/SHIN09-git/null-cone-quantum-gravity-verification/releases/tag/v0.1.0)

| Step | Evidence |
| --- | --- |
| [Finite-cut algebra](calculations/algebra.py) | Vectorization, a noncommuting complex projection, the phase bound and the smooth cutoff limit. [Output](baseline/cut-algebra.txt) |
| [Cutoff experiments](calculations/experiments.py) | 52 records at 80 and 130 decimal digits, covering hard cutoffs, smooth cutoffs, tail estimates and the free shear response. [JSONL](baseline/cut-numeric.jsonl) |
| [Independent two-level check](calculations/independent.py) | Evaluation of all 255 nonempty subsets of eight full cycles. [Output](baseline/paired-check.txt) |
| [Whole-paper symbolic checks](calculations/exact_checks.py) | The five exhaustions, exact replica examples, the joint thermal sum, the window identity, clock estimates and entropy-coefficient arithmetic. [Output](baseline/recheck-algebra.txt) |
| [Whole-paper numerical checks](calculations/numerical.py) | 44 records at 80 and 120 decimal digits, covering four replica cutoffs, four joint cuts, six rapidities, four sparse spectra and four fixed areas in the moving-window integral at each precision. [JSONL](baseline/recheck-numeric.jsonl) |
| [Phase-two and recheck tests](tests/) | Nine original closure tests and five further cutoff and spectral tests. The log records the result for each test. [Output](baseline/tests.txt) |

The five calculation outputs matched the corresponding pre-publication results after newline normalization. The public run was repeated using a separate virtual environment. Both used CPython 3.12.10, SymPy 1.14.0 and mpmath 1.3.0. The 96 numerical records illustrate the proofs and distinguish the summation prescriptions. The divergence and conditional implications are proved in the [equation audit](DERIVATION.md) and [extended derivations](RECHECK.md).

### Primary sources

The standard-library command below retrieves three versioned files into memory. It verifies their lengths and SHA-256 digests, reads the manuscript's TeX member directly from the archive and checks eleven specific source lines. These include the step after (5.38), the regular-saddle hypothesis, the filter assumption and the reference back to (5.39c). With PyMuPDF installed, the optional second command also checks 80 named PDF equation destinations and locates Axiom 1 in reference [36]. The optional outline check uses the fixed experimental HTML (lxml 6.1.0 and PyMuPDF 1.28.2) to compare 526 equation tags with PDF destinations. It counts the 45 TeX headings, 84 PDF references and four single printed equations missing from the HTML tag list. For offline use, add the source-directory option and supply the named files, including full-v1.html for the outline check. [Version fingerprints and page locators](../reference/phase2.json) · [Recorded source verification](../reference/phase2-check.txt)

~~~sh
python -B tools/check_phase2_sources.py
python -B tools/check_phase2_sources.py --pdf-pages
python -B tools/check_phase2_sources.py --outline
python -B tools/check_phase2_sources.py --source-dir ../arxiv-originals
~~~

The optional PDF check used PyMuPDF 1.28.2. The technical note can be rebuilt from [its TeX source](report/report.tex) with pdfLaTeX. The member manifest covers the note, its source and the other public files. The release page supplies separate SHA-256 checksums for the PDF and distribution ZIP.

~~~sh
python -B tools/build_report.py --phase 2 --out ../rebuilt-closure-note.pdf
python -B tools/snapshot.py --zip ../null-cone-v0.2.0-rebuilt.zip
~~~

### Review provenance

The project lead specified the question and authorized publication. OpenAI Codex derived the results, wrote the programs and prepared the reports. Separate AI review contexts examined the manuscript before comparing conclusions. The [phase-two first reading](review/FIRST_PHASE2.md) and [whole-paper first reading](review/FIRST_RECHECK.md) are public reading editions with adjusted links and typesetting. The [phase-two review](review/PHASE2_CN.md) corrects a formula number in its first reading. The [whole-paper review](review/RECHECK_CN.md) examines the strongest alternative assumptions under which finite dimension would follow. No signed human line-by-line audit or external specialist review of these results is documented as of 26 November 2026.

For version identification, the original phase-two first reading had SHA-256 ef66d125e481358a3d66420dc6ee9f281a2d08c9c8f3ba9ea65a0a7571406dbb. The original whole-paper first reading had SHA-256 7a41d7ef816a7d0cf3741e2c1dfa90e88101d1b58ca314c8e9e604e58d7e6714. These fingerprints identify the original research files. The root [SHA256SUMS](../SHA256SUMS) identifies the public editions.
