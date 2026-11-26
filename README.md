# Independent verification of null-cone quantum gravity

[中文说明](README_CN.md) · [v0.2.0 release](https://github.com/SHIN09-git/null-cone-quantum-gravity-verification/releases/tag/v0.2.0) · [Primary manuscript v1](https://arxiv.org/abs/2611.34924v1)

## Local v0.3.0-rc.1 candidate · Lean 4

Lean checks the five incompatible cutoffs of a single bounded insertion, the finite-rank inequalities behind (5.39), and the scalar series in (4.33). Use the phase-three directory for the toolchain, fully stated theorems, independent semantic review, and build logs. The earlier public releases can still be obtained at their original tags. [Lean project](phase3/README.md) · [English report](phase3/REPORT_EN.md) · [Theorem map](phase3/FORMALIZATION_MAP.md)

## Section 5.2 · Closing the last cut

What allows the resolution of the identity between two fixed states in (4.29) to be used when the last boundary is closed in (5.38)? In the fixed clock window, (5.30c) gives each orthogonal state a positive weight bounded below by the same constant. The total weight of a rank-$N$ cut therefore grows at least linearly with $N$. Re-reading the six main sections and Appendices A–E, we could verify the finite-cut estimate and identify conditions under which (5.39) follows. We did not find an independent proof that the selected cutoffs converge to the same finite uncut amplitude. The physical dimension of the four-dimensional diamond remains unresolved in this audit. [English technical note, pp. 1–3](phase2/report/report.pdf) · [逐式核验](phase2/FINDINGS.md)

| Finding | Evidence and scope |
| --- | --- |
| One finite limit would suffice | In infinite dimension, the manuscript's complete-cycle construction yields one fixed signed insertion whose amplitude tends to negative infinity. Showing finite convergence along that particular exhaustion would prove finite dimension. [Derivation](phase2/DERIVATION.md) |
| A positive value along one exhaustion can be misleading | In a two-area operator model with identical Gaussian weights, five increasing exhaustions give positive infinity, a fixed positive number, zero, a fixed negative number and negative infinity. All include every basis label. The model tests the inference from open gluing and supplies no four-dimensional gravitational solution. [Countermodel](phase2/COUNTERMODEL.md) · [Exact calculation](phase2/calculations/exact_checks.py) |
| Two alternative proof routes have identifiable inputs | A positive lower limit for the exact ratio (D.47) would suffice. The ratio evaluated in (D.49) is a one-loop regular-saddle integral. Appendix E.3 invokes (5.39c) in its verification of closed-amplitude finiteness. [Re-examination](phase2/RECHECK.md) |
| Some downstream results survive as exact statements | The absolute joint sum in (5.44) is $2p(1-p)Z_\beta$. In (5.66), a finite nonzero thermal trace gives an exact thermal-weighted mean window cost of $1/2$, even though costs of individual windows can diverge. [English note, p. 4](phase2/report/report.pdf#page=4) |

OpenAI Codex performed the analysis and computations. Separate AI contexts challenged the derivations. No external specialist review or signed human line-by-line review of this audit is documented. The public record includes the proofs, 14 tests and 96 numerical records for this phase. [中文全篇复核](phase2/REPORT_CN.md) · [Review and reproducibility](phase2/REPRODUCIBILITY.md)

From the root of this checkout, using the two pinned Python dependencies, run:

~~~sh
python -B reproduce.py --phase 2 --out ../null-cone-phase2-run --compare
~~~

## Section 4.4 · Transition amplitudes and convergence

[English report](report/report.pdf) · [LaTeX source](report/report.tex) · [Section 4.4 release v0.1.0](https://github.com/SHIN09-git/null-cone-quantum-gravity-verification/releases/tag/v0.1.0)

The first study checks equations (4.29)–(4.33) in Section 4.4 of Venkatesa Chandrasekaran's *An algebraic quantization of gravity from the null cone*, arXiv:2611.34924v1. With one real angular harmonic, one polarization, the specified Gaussian state and the specified mode rotation, the connected radial pair amplitude is absolutely convergent at every fixed positive coupling. At radial cutoff $N$, the cubic coefficient is $-iH_N$ with $H_N=\sum_{k=1}^N 1/k$. Its magnitude grows logarithmically as the cutoff is removed. The derivations and their domains are on pp. 2–5 of the report. [Primary manuscript, Section 4.4](https://arxiv.org/html/2611.34924v1#S4.SS4)

**Contributions and review.** OpenAI Codex carried out the mathematical derivations, wrote and ran the reproducibility checks, and drafted this report. This release has not been reviewed by an external specialist.

| Evidence | Finding |
| --- | --- |
| Proved | (4.29) and (4.30) give the one-cut matrix element and its absolute bound for finite-norm states and unitary propagators. (4.31) controls independent projection cutoffs for finitely many cuts. |
| Conditional | Matching the boundary data and composing the admitted evolutions give the spacetime interpretation. Equation (4.32) chooses the widths and phase. |
| Proved for that preparation | With $x=4G_N\hbar/\mathcal A=1/s$, the centered overlap is $C(x)=x^2\operatorname{Li}_2(e^{-2ix})/2$. Its hard-cutoff error is at most $x^2/(2N)$. The report supplies the sharper oscillatory bound, alternative regulators and an explicit remainder for the weak-coupling expansion. |
| Numerical support | 127 records cover 85- and 125-decimal-digit evaluations and finite checks. At $s=10$ the observed result is approximately $0.006703874007446236-0.002609993579151187i$. |
| Open interpretation | Identifying the chosen rotation with a geometric translation on a finite null boundary requires an endpoint-preserving map. |
| Unverified | General self-adjoint gravitational evolution, common domains for arbitrary continuum sources and ultraviolet completeness of four-dimensional gravity do not follow from these results. |

### The two counterexamples

1. **Uncentered source.** In the very same Gaussian product vacuum, the uncentered positive quadratic source has infinite limiting form on every nonzero state. Its centered vacuum vector has finite norm and gives (4.33).
2. **Two cuts.** A block-diagonal Walsh unitary gives a matrix element of $1/3$ while each block contributes one unit to the sum of absolute path weights. This disproves joint absolute summability of the fully expanded paths under the Hilbert-space assumptions alone. The estimate for independent cut projections still holds.

Both propositions and proofs appear on p. 6. Their conclusions concern the named extensions. The status of the general gravitational theory remains open.

### Reproduce the calculations

Download the v0.1.0 release archive or check out the v0.1.0 Git tag. Enter the folder containing this README and keep the virtual environment and results outside it. The reference run used CPython 3.12.10 with SymPy 1.14.0 and mpmath 1.3.0. The lock file includes the SHA-256 of each universal wheel. On Windows PowerShell use:

~~~powershell
py -3.12 -m venv ../null-cone-env
../null-cone-env/Scripts/python.exe -m pip install --only-binary=:all: --require-hashes -r requirements.txt
../null-cone-env/Scripts/python.exe -B tools/snapshot.py
../null-cone-env/Scripts/python.exe -B reproduce.py --out ../null-cone-run --compare
~~~

On macOS or Linux:

~~~sh
python3.12 -m venv ../null-cone-env
../null-cone-env/bin/python -m pip install --only-binary=:all: --require-hashes -r requirements.txt
../null-cone-env/bin/python -B tools/snapshot.py
../null-cone-env/bin/python -B reproduce.py --out ../null-cone-run --compare
~~~

Use a fresh output directory for each run. After dependency installation the scientific checks take no network input. The runner executes symbolic integration, the high-precision comparisons, the 11 unit tests, and a separate standard-library script. It saves full stdout and stderr for each step, the commands, versions, exit codes and output hashes. The frozen record contains nine files. `--compare` compares all nine byte for byte, including the interpreter version. Other interpreters or system math libraries can change output digits. Omitting `--compare` retains every mathematical and numerical assertion. [Baseline manifest](baseline/run.json) · [Numerical records](baseline/numerical.jsonl) · [Independent checks](tests/independent_checks.py)

After selecting the Python interpreter as above, these optional commands use only the standard library. Rebuilding the PDF also requires pdfLaTeX with its usual mathematics packages, AMS fonts, geometry, xcolor and hyperref.

~~~sh
python -B tools/check_paper.py
python -B tools/build_report.py --out ../rebuilt-report.pdf
python -B tools/snapshot.py --zip ../rebuilt-snapshot.zip
~~~

The first command reads the two official v1 files over HTTPS and verifies their lengths and digests. The archive does not redistribute the manuscript. The second compiles the included TeX twice. Different TeX distributions may produce different PDF bytes. The last command verifies the exact member list and rebuilds the ZIP from the frozen files. [Paper fingerprints](reference/paper.json) · [Version record](VERSION.md)

### Authorship and review

The project lead defined the question and scope and authorized the published phase-one and phase-two releases. OpenAI Codex developed the primary proofs, wrote and ran the symbolic and numerical programs, and prepared the report and release files. A separate AI context read the manuscript before seeing the first analysis, developed adversarial checks and wrote the standard-library script. The analytic arguments are available for inspection. Model agreement supplies no independent mathematical proof.

As of 26 November 2026 the project record contains no signed or documented human line-by-line mathematical audit and no external peer-review report for this verification. The studied paper's author is credited for the paper. For citation and the public-release terms, see the [version record](VERSION.md) and [licensing notice](LICENSE.md).
