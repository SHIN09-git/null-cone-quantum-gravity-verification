# Closing the last cut: a Lean 4 audit of the v1 argument

**Counterexample found.** In one infinite-dimensional complex Hilbert space, the open identity gluing formula converges absolutely for every pair of external states. Five increasing finite-rank orthogonal projections converge strongly to the identity. For one fixed bounded insertion, their unnormalised closed matrix elements have five different limits. One sequence reproduces the positive reference value at every stage. The example tests the mathematical inference at the last cut in §5.2. The dimension of the four-dimensional gravitational state space remains undetermined. [Combined theorem](NullCone/Counterexample.lean) · [Paper v1](https://arxiv.org/abs/2611.34924v1)

## The operators and their five limits

Take two countably infinite families of orthonormal area states, with eigenvalues 1 and 3. The one-sided space is the complex ℓ² space of their disjoint union B. The two-sided space is the coefficient realisation ℓ²(B×B), indexed by a left ket and a conjugate right ket. At the centre 3 and width 1, the Gaussian in the paper yields W=C†C=wI with w=exp(−3). The identification is checked by continuous functional calculus for the actual self-adjoint area operator. The one-sided flip F swaps the two states at each index. The two-sided observable O=−F⊗F̄ flips both coordinates. The boost acts only on the right. At rapidity π its relative phase is one radian, and the normalised one-pair preparation gives δ=1−cos(1)>0. [Gaussian function on the area](NullCone/Area.lean) · [Coordinate operators](NullCone/Model.lean) · [Reference preparation](NullCone/Amplitude.lean)

The cutoff selecting r left-family labels and n right-family labels prepares a vector with coefficients ⟨eᵢ,CPeⱼ⟩. Its squared norm is T. The measured change Δ is the difference of the boosted and unboosted expectations in the unit vector. The signed insertion is X=U†OU−O−δI/2. For r≥n and r+n>0, contraction in the full two-label Hilbert space gives

$$
T=w(r+n),\qquad \Delta=\frac{2n\delta}{r+n},\qquad
Z=\operatorname{Re}\langle v,Xv\rangle=\frac{w\delta}{2}(3n-r).
$$

| Number r for n=1,2,… | Exact signed amplitude | Limit |
| --- | --- | --- |
| n | wδn | +∞ |
| 3n−2 | wδ | wδ |
| 3n | 0 | 0 |
| 3n+2 | −wδ | −wδ |
| 7n | −2wδn | −∞ |

**Rigorously verified.** Every row uses the same area, Gaussian, flip, boost, insertion and reference state. The projections exhaust every basis label and converge in norm on every fixed external vector. The second row reproduces the signed reference value while its normalised response tends to δ/2. The directed net over all finite label sets consequently has no finite limit. The model supplies no realisation of the local shear dynamics or the full four-dimensional gravitational constraints. [Strong exhaustion](NullCone/Cutoffs.lean) · [Finite contractions](NullCone/Amplitude.lean) · [Five limits](NullCone/Limits.lean)

## When finite dimension follows

**Rigorously verified.** The ordinary extended positive trace of W is the supremum of its diagonal sums over finite orthonormal families. The finite-cut value equals the matrix trace of the compression. If W≥cI with one c>0 on all of H, each family of size N contributes at least cN. Infinite dimension permits arbitrarily large such N. Hence the ordinary trace is finite exactly when H is finite-dimensional. An arbitrary bounded preparation C has a square-summable two-sided matrix precisely when the ordinary trace of C†C is finite. It can be normalised to a unit preparation if C is also nonzero. These results identify the strength of requiring the uncut ordinary Hilbert vector to exist. [Positive trace](NullCone/Trace.lean) · [Hilbert–Schmidt characterisation](NullCone/HilbertSchmidt.lean)

**Conditionally valid.** On a cut with |Δ|≤δ/4, the actual weight and signed amplitude obey
$$
Z_P=T_P(\Delta_P-\delta/2)\le -(c\delta/4)\operatorname{rank} P .
$$
A uniform finite lower bound on these same small-response cuts rules out unbounded rank. For a finite-limit hypothesis, arbitrarily large qualifying cuts must occur in every tail of that particular filter. Lean separately constructs finite orthonormal families in the infinite-dimensional case, proves the negative rank bound, chooses fixed width and cycle-length parameters, and derives the finite-dimensional implication. A second theorem starts from a finite cover by closed invariant bands, a bound on the centred operators in each band, and control of the response by the actual weighted moment. It constructs a low-moment cut extending any specified finite subspace. Diagonalising the compressed weight controls the trace even when the cut projection fails to commute with the weight or the area. A uniform lower bound on every qualifying extension then gives finite dimension. The application to gravity still requires the spectral and geometric data to come from the physical preparation, and the lower bound to hold for its unnormalised closure. A second sufficient hypothesis is a finite positive functional on B(H) agreeing with the geometric weight on every finite projection. [Dimension](NullCone/Dimension.lean) · [Band dilution](NullCone/Dilution.lean) · [Response bound](NullCone/Response.lean) · [Finite functional](NullCone/Functional.lean)

**Counterexample found.** With identity evolution on ℓ², every open matrix element is an absolutely convergent Parseval sum, bounded in absolute sum by the product of the two vector norms. The ordinary positive identity trace in that very space is infinite. This independently answers the open-to-closed implication even before introducing signed insertions. [Open and closed sums](NullCone/Trace.lean)

## The scalar amplitude and perturbation theory

**Rigorously verified.** With x=1/s, the positive radial modes in (4.33) give
$$
C(x)=\frac{x^2}{2}\sum_{k\ge1}\frac{e^{-2ikx}}{k^2}.
$$
The sum of the term norms is π²x²/12 for every real x. The error after retaining N≥1 modes is at most x²/(2N). The polylogarithm here is its convergent dilogarithm series on the closed unit disk. For a fixed hard cutoff, one sixth of the actual third derivative at x=0 is −iH_N. Its negative imaginary part minus log N tends to Euler's constant. The third-order coefficient is the issue raised immediately after (4.33), in (4.34). [Scalar series and real derivatives](NullCone/Series.lean) · [Physical variables and mode normalisation](review/SERIES.md) · [Original equation](https://arxiv.org/html/2611.34924v1#S4.E33)

For the function after summation, C(x)/x² tends to π²/12 from both sides. Its imaginary part divided by x³ tends to −∞ as x decreases to zero through all positive real values. Subtracting the verified quadratic term thus leaves no finite right cubic coefficient. A cutoff varying as the integer part of 1/(2x) controls the tail while the initial sine sum supplies a growing harmonic contribution. The formalisation establishes the divergent direction and the failure of an ordinary finite third-order expansion. The exact logarithmic correction and finite part of that expansion have not been formalised. [Uncut amplitude](NullCone/Perturbation.lean)

## Interpretation and checks

**Unverified physical input.** The reduction to the stated scalar modes uses the paper's preparation, polarisation, harmonic and contractions. The operator construction supplies the specified Hilbert-space data. A proof of the gravitational cut equivalence under removal of the final free index, a realisation of all four-dimensional constraints, and ultraviolet completeness for general amplitudes remain open in this audit. Separate AI contexts wrote blind criteria, checked theorem strength and cross-reviewed the two extensions authored during review. The kernel checks the proof terms. The project has no recorded independent human peer review. [Assumptions](ASSUMPTIONS.md) · [Source-to-theorem map](FORMALIZATION_MAP.md) · [Independent semantic review](review/INDEPENDENT.md) · [Build and kernel logs](evidence/run.json)

