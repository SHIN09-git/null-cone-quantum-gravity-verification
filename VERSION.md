# Version record

## v0.3.0-rc.1 · Local Lean verification candidate

The candidate branches from public v0.2.0, commit `44df2c1e4915c0e654dd5907d91b775e83f31326`. The proof toolchain and all dependency revisions are locked in phase3. The archive root for this candidate is `null-cone-gravity-v0.3.0-rc.1/`. [Phase-three project](phase3/README.md) · [Machine evidence](phase3/evidence/run.json)

## v0.2.0 · 26 November 2026

*Closing the last cut in null-cone quantum gravity*. The phase-two note audits (5.30c)–(5.39) against Sections 2–6 and Appendices A–E, with follow-on checks of (5.44) and (5.66). Cite the Null-cone amplitude verification project, version v0.2.0, and the immutable tagged release when referring to this analysis. The findings concern the fixed v1 manuscript. [Tagged release](https://github.com/SHIN09-git/null-cone-quantum-gravity-verification/releases/tag/v0.2.0) · [English note](phase2/report/report.pdf) · [中文报告](phase2/REPORT_CN.md)

The distribution uses the archive root **null-cone-gravity-v0.2.0/**. Its per-member hashes are listed in SHA256SUMS. The downloadable checksums identify the ZIP and standalone phase-two PDF. All six offline commands and both output streams per command appear in the [phase-two manifest](phase2/baseline/run.json). The [source record](reference/phase2.json) pins the manuscript PDF and source tarball, the TeX member, selected source lines, printed equation locations and the version of reference [36]. The phase-one report and its public baseline remain available in this distribution and at its original tag.

## v0.1.0 · Section 4.4

**v0.1.0 · 26 November 2026.** Scope covers arXiv:2611.34924v1, Section 4.4, equations (4.29) through (4.33) and mathematical checks of those equations. The weak-coupling expansion is derived from the scalar amplitude in (4.33). The release contains two counterexamples to precisely stated extensions.

Suggested citation: Null-cone amplitude verification project. *An Independent Verification of Null-Cone Quantum Gravity: Transition Amplitudes and Convergence.* v0.1.0, 26 November 2026. [Report and reproducibility archive](https://github.com/SHIN09-git/null-cone-quantum-gravity-verification/releases/tag/v0.1.0). Record the distribution SHA-256 if identifying a particular copy. The arXiv identifier belongs to the studied paper.

### Manuscript identity

Venkatesa Chandrasekaran, *An algebraic quantization of gravity from the null cone*. v1 was submitted on 25 November 2026 at 18:58:55 UTC. The displayed equations on PDF pp. 32, 33 and 34 are respectively (4.29)–(4.30), (4.31)–(4.32) and (4.33). The digit strings below identify the bytes recorded on 26 November 2026. They are SHA-256 digests, not a digital signature by the author. [arXiv version history](https://arxiv.org/abs/2611.34924v1) · [Machine-readable record](reference/paper.json)

| Object | Bytes | SHA-256 |
| --- | ---: | --- |
| v1 PDF | 1,979,526 | `d17caccbee57cfbee6fc2eeed2e5a53467c9401be979fd2952aa2bf92d5443af` |
| v1 source archive | 904,770 | `1251f05ae2fac0bc307286550e115f3a9ef9228187822b9f40aad9c33b3407be` |

### Research inputs and release changes

The numerical, symbolic and amplitude programs below were copied byte for byte from the frozen first-stage run. The independent check was moved into the test directory without changing its bytes. The run on which these input fingerprints were recorded started at 06:41:19 UTC on 26 November 2026.

| Packaged program | First-stage SHA-256 |
| --- | --- |
| `calculations/amplitudes.py` | `b17ff251e64c2302d2034bbc00062bb82ab239573bccd63eebadd69d5f71df43` |
| `calculations/symbolic.py` | `fd3a2889c05af51ab2d17b14673e7e7e77f999a7d5c2543cfd0e21fdbd45d67c` |
| `calculations/numerical.py` | `54e4801e7a4c1da2153a8f94ad18441f0a137004a1c56b5e94f329e7d43c711d` |
| `tests/independent_checks.py` | `1b1bedda090f9cc4d42bfce96546eedffea64ba8827131b970cf758cfb9d0996` |

The separately written first-pass mathematical review was fingerprinted before comparison to the primary analysis. Its private draft has SHA-256 `0a28db1bb1ee43a03f671465d5dc3368f74616f775414a2fc910ebf1b80e882f`. The public derivations of its two counterexamples are on p. 6 of the report. The independent script reproduces its finite checks.

For this version the project selected unit tests within the stated scope, retained a single multi-cut construction and added an exact unit test for its unitarity. A portable driver writes standard output, error streams and the run manifest without local executable paths. Symbolic, numerical and standard-library outputs agree line for line with the frozen research run after newline normalization. The 11 unit tests in this release are recorded by name. [Unit-test log](baseline/tests.txt) · [Run manifest](baseline/run.json)

### Rebuilding the distribution

The public title and review disclosure appear on the report's first page and in both READMEs. The v0.1.0 tag and the release ZIP contain the same project files. The manifest `SHA256SUMS` covers each member except itself. In a Git checkout the checker skips the root `.git` metadata entry. The distribution checksum covers the entire ZIP, including that manifest. The ZIP uses the root `null-cone-4.4-v0.1.0/`, sorted member names, uncompressed storage, ordinary file mode 0644 and a constant member timestamp of 2026-11-26 00:00:00. The timestamp is a packaging convention. The run logs normalize text newlines to LF. The PDF source sets stable dates and omits volatile PDF metadata. The reference PDF was built with MiKTeX pdfTeX 1.40.28. Instructions for checking both layers of the snapshot and rebuilding the PDF appear in the [README](README.md).
