# Five closure values at identical cutoff ranks

The Phase 2 two-area model admits five increasing exhaustions with the same rank in each band at each stage. Their signed amplitudes tend to positive infinity, a positive constant, zero, a negative constant and negative infinity. Thus a regulator that fixes only the two band counts still leaves the closure value undetermined in this model. [Original prefix cutoffs](../../RECHECK.md#2-同一个正有限数可以怎样出现) · [SHIN09’s Lean verification of the prefix limits](https://github.com/SHIN09-git/null-cone-quantum-gravity-verification/blob/d2021a05c55554032f4e1e3c5272756366b8d54c/phase3/NullCone/Limits.lean)

## Finite contraction

Let $A$ and $B$ be the finite sets of indices kept in the first and second area bands. For each index, the diagonal tensor states $a_j\otimes\bar a_j$ and $b_j\otimes\bar b_j$ span an invariant block. The simultaneous negative swap interchanges these states with a minus sign. The right boost multiplies the second coefficient by a relative phase $z$ after a common phase is removed. The model has $w=e^{-3}$, $z=e^{i}$, and $\delta=1-\operatorname{Re}z>0$. [Operator construction](../../calculations/exact_checks.py)

Each complete pair contributes $2w\delta$ to the change of the swap expectation. Each occupied state contributes $w$ to the squared norm. Subtracting $\delta/2$ times this norm gives

$$
Z(A,B)=\frac{w\delta}{2}\bigl(4|A\cap B|-|A|-|B|\bigr).
$$

Write $C(e,o)$ for the first $e$ even and first $o$ odd indices, numbered from zero. At each $n\ge1$, keep $A_n=C(5n,n)$ in the first band and choose $B_n=C(b,6n-b)$ in the second. Both have rank $6n$, giving total rank $12n$ and identical Gaussian mass $12nw$ in all five cases.

| Second-band even count $b$ | Complete pairs $\lvert A_n\cap B_n\rvert$ | $Z/(w\delta)$ |
| --- | ---: | ---: |
| $5n$ | $6n$ | $6n$ |
| $2n+1$ | $3n+1$ | $2$ |
| $2n$ | $3n$ | $0$ |
| $2n-1$ | $3n-1$ | $-2$ |
| $n$ | $2n$ | $-2n$ |

Every even and odd prefix grows by inclusion and has length at least $n$. Therefore each sequence eventually contains any prescribed finite set. The diagonal projections converge strongly to the identity in the two-band Hilbert space. The physical step at Eq. (5.38) remains open. Prove2Me’s related finite-dimension theorem assumes convergence of the selected closed-sewing amplitude. [Eq. (5.38)](https://arxiv.org/html/2611.34924v1#S5.E38) · [Prove2Me theorem](https://prove2.me/theorems/05ba10eb-241a-575f-b92b-89c7b1b7ba15) · [Mission resources](https://prove2.me/missions/Algebraic_quantization_of_gravity_from_the_null_cone/resources)

## Replay

The Lean file derives the finite identity from the complex two-coordinate swap, then proves the five values, both ranks, nesting and exhaustion for arbitrary stages. Its environment matches Prove2Me’s Lean 4.33.1 with Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`. From a Mathlib checkout at that revision, with its cache installed, run the following command using the path to this supplement. [Lean proof](EqualRank.lean)

```sh
lake env lean -DwarningAsError=true /path/to/phase2/supplements/equal_rank/EqualRank.lean
```

From the root of this repository, the independent numerical check calls the Phase 2 complex operator on the actual labels in all five routes for stages 1 through 32. It also checks the exact integer counts. It uses only the Python standard library. [Operator replay](check_operators.py)

```sh
python -B -m phase2.supplements.equal_rank.check_operators
```

This supplement extends the Null-cone amplitude verification project’s v0.2.0 two-area example. The release candidate separately verifies the original prefix schedules on its pinned Lean 4.24 toolchain. [Tagged upstream project](https://github.com/SHIN09-git/null-cone-quantum-gravity-verification/tree/v0.3.0-rc.1/phase3)
