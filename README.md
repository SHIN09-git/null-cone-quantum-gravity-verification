# An Independent Verification of Null-Cone Quantum Gravity: Transition Amplitudes and Convergence

*A Reproducibility Study of Section 4.4 of arXiv:2611.34924v1*

[光锥量子引力的独立核验：跃迁振幅与收敛性（中文）](README_CN.md) · [English technical report (PDF)](report/report.pdf) · [Report source](report/report.tex) · [Release v0.1.0](https://github.com/SHIN09-git/null-cone-quantum-gravity-verification/releases/tag/v0.1.0)

This independent audit checks equations (4.29)–(4.33) in Section 4.4 of Venkatesa Chandrasekaran's *An algebraic quantization of gravity from the null cone*, arXiv:2611.34924v1. With one real angular harmonic, one polarization, the specified Gaussian state and the specified mode rotation, the connected radial pair amplitude is absolutely convergent at every fixed positive coupling. At radial cutoff $N$, the cubic coefficient is $-iH_N$ with $H_N=\sum_{k=1}^N 1/k$. Its magnitude grows logarithmically as the cutoff is removed. The derivations and their domains are on pp. 2–5 of the report. [Primary manuscript, Section 4.4](https://arxiv.org/html/2611.34924v1#S4.SS4)

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

The project lead defined the question and scope and authorized this release. OpenAI Codex developed the primary proofs, wrote and ran the symbolic and numerical programs, and prepared the report and release files. A separate AI context read the manuscript before seeing the first analysis, developed adversarial checks and wrote the standard-library script. The analytic arguments are available for inspection. Model agreement supplies no independent mathematical proof.

As of 26 November 2026 the project record contains no signed or documented human line-by-line mathematical audit and no external peer-review report for this verification. The studied paper's author is credited for the paper. For citation and the public-release terms, see the [version record](VERSION.md) and [licensing notice](LICENSE.md).
