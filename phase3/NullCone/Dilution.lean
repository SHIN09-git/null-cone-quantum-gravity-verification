import NullCone.Dimension
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.RingTheory.Finiteness.Finsupp

/-! # Adding finite cuts inside an infinite-dimensional spectral band -/

noncomputable section

open scoped BigOperators InnerProductSpace
open Submodule InnerProductSpace NullCone.Trace

namespace NullCone.Dilution

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- A finite collection of subspaces with dense joint span cannot all have finite dimension
if the ambient space is infinite-dimensional. Orthogonality of the bands is unnecessary. -/
theorem exists_infinite_band {ι : Type*} [Finite ι] (V : ι → Submodule ℂ H)
    (hcover : (⨆ i, V i).topologicalClosure = ⊤) (hH : ¬ FiniteDimensional ℂ H) :
    ∃ i, ¬ FiniteDimensional ℂ (V i) := by
  classical
  by_contra! hall
  letI : ∀ i, FiniteDimensional ℂ (V i) := hall
  let S := ⨆ i, V i
  have htop : S = ⊤ :=
    S.closed_of_finiteDimensional.submodule_topologicalClosure_eq.symm.trans hcover
  letI : FiniteDimensional ℂ (⊤ : Submodule ℂ H) := htop ▸ (inferInstance : FiniteDimensional ℂ S)
  exact hH (Submodule.topEquiv : (⊤ : Submodule ℂ H) ≃ₗ[ℂ] H).finiteDimensional

omit [CompleteSpace H] in
/-- The kernel of the projection of the band onto the old cut has infinite dimension.
Gram-Schmidt in this kernel supplies actual orthonormal vectors, even for a nonclosed band. -/
theorem exists_band_extension (E V : Submodule ℂ H) [FiniteDimensional ℂ E]
    (hV : ¬ FiniteDimensional ℂ V) (n : ℕ) :
    ∃ z : Fin n → H, Orthonormal ℂ z ∧ ∀ j, z j ∈ V ∧ z j ∈ Eᗮ := by
  classical
  let f := E.orthogonalProjection.toLinearMap.comp V.subtype
  have hker : ¬ FiniteDimensional ℂ (LinearMap.ker f) := by
    intro hfinite
    letI : FiniteDimensional ℂ (V ⧸ LinearMap.ker f) :=
      FiniteDimensional.of_injective f.quotKerEquivRange.toLinearMap f.quotKerEquivRange.injective
    exact hV (Module.Finite.of_submodule_quotient (LinearMap.ker f))
  let b := Module.Basis.ofVectorSpace ℂ (LinearMap.ker f)
  let I := Module.Basis.ofVectorSpaceIndex ℂ (LinearMap.ker f)
  letI : Infinite I := not_finite_iff_infinite.mp (fun _ => hker (FiniteDimensional.of_fintype_basis b))
  let j : Fin n → I := fun i => Infinite.natEmbedding I i.val
  have hj : Function.Injective j := (Infinite.natEmbedding I).injective.comp Fin.val_injective
  let u := gramSchmidtNormed ℂ (b ∘ j)
  have hu : Orthonormal ℂ u := gramSchmidtNormed_orthonormal (b.linearIndependent.comp j hj)
  let inclusion := V.subtypeₗᵢ.comp (LinearMap.ker f).subtypeₗᵢ
  refine ⟨inclusion ∘ u, hu.comp_linearIsometry inclusion, fun i => ⟨(u i).val.property, ?_⟩⟩
  rw [← E.ker_orthogonalProjection]
  exact (u i).property

/-- The diagonal of the projection onto the outside of the specified band. -/
def outsideMass (V : Submodule ℂ H) (x : H) : ℝ := ‖Vᗮ.orthogonalProjection x‖ ^ 2

private theorem outsideMass_eq_diagonal (V : Submodule ℂ H) (x : H) :
    outsideMass V x = (⟪x, Vᗮ.starProjection x⟫_ℂ).re := by
  change ‖Vᗮ.orthogonalProjection x‖ ^ 2 = RCLike.re (⟪x, Vᗮ.starProjection x⟫_ℂ)
  rw [inner_re_symm]
  exact (Vᗮ.re_inner_starProjection_eq_normSq x).symm

private theorem outsideMass_unit_le (V : Submodule ℂ H) (x : H) (hx : ‖x‖ = 1) :
    outsideMass V x ≤ 1 := by
  have h := Vᗮ.norm_orthogonalProjection_apply_le x
  rw [hx] at h
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans_eq (one_pow _)

omit [CompleteSpace H] in
private theorem orthonormal_sum {α β : Type*} {a : α → H} {b : β → H}
    (ha : Orthonormal ℂ a) (hb : Orthonormal ℂ b)
    (hab : ∀ i j, ⟪a i, b j⟫_ℂ = 0) : Orthonormal ℂ (Sum.elim a b) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  cases i with
  | inl i =>
    cases j with
    | inl j => simpa using (orthonormal_iff_ite.mp ha) i j
    | inr j => simp [hab]
  | inr i =>
    cases j with
    | inl j => simp [inner_eq_zero_symm.mpr (hab j i)]
    | inr j => simpa using (orthonormal_iff_ite.mp hb) i j

/-- Extend the old subspace to a cut of rank exactly its old rank plus `n`. The trace of
the outside-band projection on this cut is at most the old rank. -/
theorem exists_diluted_cut (E V : Submodule ℂ H) [FiniteDimensional ℂ E]
    (hV : ¬ FiniteDimensional ℂ V) (n : ℕ) :
    ∃ e : Fin (Module.finrank ℂ E + n) → H, Orthonormal ℂ e ∧
      E ≤ Submodule.span ℂ (Set.range e) ∧
      Module.finrank ℂ (Submodule.span ℂ (Set.range e)) = Module.finrank ℂ E + n ∧
      (∑ i, outsideMass V (e i)) ≤ Module.finrank ℂ E := by
  classical
  let B := stdOrthonormalBasis ℂ E
  let a := E.subtypeₗᵢ ∘ B
  have ha : Orthonormal ℂ a := B.orthonormal.comp_linearIsometry E.subtypeₗᵢ
  obtain ⟨z, hz, hmem⟩ := exists_band_extension E V hV n
  let w := Sum.elim a z
  have hw : Orthonormal ℂ w := orthonormal_sum ha hz
    (fun i j => E.inner_right_of_mem_orthogonal (B i).property (hmem j).2)
  let j : Fin (Module.finrank ℂ E) ⊕ Fin n ≃ Fin (Module.finrank ℂ E + n) := finSumFinEquiv
  let e := w ∘ j.symm
  have he : Orthonormal ℂ e := hw.comp j.symm j.symm.injective
  refine ⟨e, he, ?_, by simpa using finrank_span_eq_card he.linearIndependent, ?_⟩
  · intro x hx
    let xE : E := ⟨x, hx⟩
    have hexp := congrArg E.subtype (B.sum_repr xE)
    rw [map_sum] at hexp
    change E.subtype xE ∈ _
    rw [← hexp]
    apply Submodule.sum_mem
    intro i _
    rw [map_smul]
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨j (Sum.inl i), by simp [e, w, a]⟩
  · rw [← Equiv.sum_comp j (fun i => outsideMass V (e i))]
    simp only [e, Function.comp_apply, Equiv.symm_apply_apply, w, Fintype.sum_sum_type,
      Sum.elim_inl, Sum.elim_inr]
    have hz0 (i : Fin n) : outsideMass V (z i) = 0 := by
      simp [outsideMass, V.orthogonalProjection_orthogonal_apply_eq_zero (hmem i).1]
    simp only [hz0, Finset.sum_const_zero, add_zero]
    calc
      _ ≤ ∑ _ : Fin (Module.finrank ℂ E), (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => outsideMass_unit_le V _ (ha.norm_eq_one i)
      _ = _ := by simp

/-- The outside mass is the trace of the compression of the outside projection; hence a
change to any orthonormal basis of the cut preserves it, including to a weight eigenbasis. -/
theorem outside_sum_basis_independent (V : Submodule ℂ H) {n : ℕ} {e : Fin n → H}
    (he : Orthonormal ℂ e) (b : OrthonormalBasis (Fin n) ℂ (Submodule.span ℂ (Set.range e))) :
    (∑ i, outsideMass V (b i : H)) = ∑ i, outsideMass V (e i) := by
  let P := Submodule.span ℂ (Set.range e)
  letI : FiniteDimensional ℂ P := FiniteDimensional.span_of_finite ℂ (Set.finite_range e)
  let B := Module.Basis.span he.linearIndependent
  have hB : Orthonormal ℂ B := by
    apply P.subtypeₗᵢ.orthonormal_comp_iff.mp
    convert he using 1
    funext i
    exact Module.Basis.span_apply he.linearIndependent i
  let a := B.toOrthonormalBasis hB
  have ha (i : Fin n) : (a i : H) = e i := by
    simp only [a, Module.Basis.coe_toOrthonormalBasis, B, Module.Basis.span_apply]
  simp only [outsideMass_eq_diagonal]
  calc
    _ = (LinearMap.trace ℂ P (P.orthogonalProjection ∘L Vᗮ.starProjection ∘L P.subtypeL).toLinearMap).re :=
      cutWeight_eq_trace_compression Vᗮ.starProjection P b
    _ = cutWeight Vᗮ.starProjection (fun i => (a i : H)) :=
      (cutWeight_eq_trace_compression Vᗮ.starProjection P a).symm
    _ = _ := by simp only [cutWeight, ha]

/-- Finite spectral sum for the normalized moment. Here `w` weights a complete orthonormal
basis of the cut, such as an eigenbasis of its positive compressed density. -/
theorem weighted_moment_le (V : Submodule ℂ H) {n k : ℕ} (hn : 0 < n)
    {u : Fin n → H} (hu : Orthonormal ℂ u) (q : H → ℝ) (w : Fin n → ℝ) {c ε A : ℝ}
    (hc : 0 < c) (hw : ∀ i, c ≤ w i ∧ w i ≤ 1)
    (hq : ∀ x, ‖x‖ = 1 → q x ≤ ε ^ 2 + A ^ 2 * outsideMass V x)
    (hout : ∑ i, outsideMass V (u i) ≤ k) :
    (∑ i, w i * q (u i)) / (∑ i, w i) ≤ ε ^ 2 + A ^ 2 * k / (c * n) := by
  have hsum : c * (n : ℝ) ≤ ∑ i, w i := by
    calc
      c * (n : ℝ) = ∑ _ : Fin n, c := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun i _ => (hw i).1
  have hcn : 0 < c * (n : ℝ) := mul_pos hc (Nat.cast_pos.mpr hn)
  have hT := hcn.trans_le hsum
  have hpoint (i : Fin n) : w i * q (u i) ≤ ε ^ 2 * w i + A ^ 2 * outsideMass V (u i) := by
    have hq' := mul_le_mul_of_nonneg_left (hq _ (hu.norm_eq_one i)) (hc.le.trans (hw i).1)
    have hmass : 0 ≤ outsideMass V (u i) := sq_nonneg _
    have hpenalty := mul_le_mul_of_nonneg_right (hw i).2
      (mul_nonneg (sq_nonneg A) hmass)
    nlinarith only [hq', hpenalty]
  have hnum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpoint i)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hnum
  have hnum' := hnum.trans (add_le_add_left (mul_le_mul_of_nonneg_left hout (sq_nonneg A)) _)
  calc
    _ ≤ (ε ^ 2 * (∑ i, w i) + A ^ 2 * k) / (∑ i, w i) :=
      div_le_div_of_nonneg_right hnum' hT.le
    _ = ε ^ 2 + A ^ 2 * k / (∑ i, w i) := by rw [add_div, mul_div_cancel_right₀ _ hT.ne']
    _ ≤ _ := add_le_add_left (div_le_div_of_nonneg_left (by positivity) hcn hsum) _

/-- For a single chosen cut the unweighted outside fraction and the normalized moment
are both controlled. The moment estimate holds in every basis carrying weights in [c,1]. -/
theorem exists_cut_fraction_and_moment (E V : Submodule ℂ H) [FiniteDimensional ℂ E]
    (hV : ¬ FiniteDimensional ℂ V) (n : ℕ) (hn : 0 < n) (q : H → ℝ) {c ε A : ℝ}
    (hc : 0 < c) (hq : ∀ x, ‖x‖ = 1 → q x ≤ ε ^ 2 + A ^ 2 * outsideMass V x) :
    ∃ e : Fin (Module.finrank ℂ E + n) → H, Orthonormal ℂ e ∧
      E ≤ Submodule.span ℂ (Set.range e) ∧
      Module.finrank ℂ (Submodule.span ℂ (Set.range e)) = Module.finrank ℂ E + n ∧
      (∑ i, outsideMass V (e i)) / ((Module.finrank ℂ E + n : ℕ) : ℝ) ≤
        Module.finrank ℂ E / ((Module.finrank ℂ E + n : ℕ) : ℝ) ∧
      ∀ (b : OrthonormalBasis (Fin (Module.finrank ℂ E + n)) ℂ (Submodule.span ℂ (Set.range e)))
        (w : Fin (Module.finrank ℂ E + n) → ℝ), (∀ i, c ≤ w i ∧ w i ≤ 1) →
        (∑ i, w i * q (b i : H)) / (∑ i, w i) ≤
          ε ^ 2 + A ^ 2 * Module.finrank ℂ E / (c * ((Module.finrank ℂ E + n : ℕ) : ℝ)) := by
  obtain ⟨e, he, hE, hr, hout⟩ := exists_diluted_cut E V hV n
  refine ⟨e, he, hE, hr, div_le_div_of_nonneg_right hout (by positivity), ?_⟩
  intro b w hw
  apply weighted_moment_le V (Nat.add_pos_right _ hn)
    (b.orthonormal.comp_linearIsometry (Submodule.span ℂ (Set.range e)).subtypeₗᵢ) q w hc hw hq
  change (∑ i, outsideMass V (b i : H)) ≤ _
  rwa [outside_sum_basis_independent V he b]

/-- A self-adjoint centered area operator preserving a closed band also preserves its
orthogonal complement. Splitting the input into these two parts proves the unit-vector
quadratic-form estimate used for the finite moment. -/
theorem spread_le_of_invariant_band (V : Submodule ℂ H) [CompleteSpace V] (S : H →L[ℂ] H)
    (hS : S.toLinearMap.IsSymmetric) (hinv : ∀ x ∈ V, S x ∈ V) {ε A : ℝ} (hε : 0 ≤ ε)
    (hband : ∀ x ∈ V, ‖S x‖ ≤ ε * ‖x‖) (hglobal : ‖S‖ ≤ A) (x : H) (hx : ‖x‖ = 1) :
    ‖S x‖ ^ 2 ≤ ε ^ 2 + A ^ 2 * outsideMass V x := by
  let y := V.starProjection x
  let z := Vᗮ.starProjection x
  have hy : y ∈ V := V.starProjection_apply_mem x
  have hz : z ∈ Vᗮ := Vᗮ.starProjection_apply_mem x
  have hsum : y + z = x := by
    dsimp [y, z]
    rw [V.starProjection_orthogonal']
    simp
  have hSz : S z ∈ Vᗮ := by
    apply (V.mem_orthogonal _).mpr
    intro t ht
    change ⟪t, S.toLinearMap z⟫_ℂ = 0
    rw [← hS t z]
    exact V.inner_right_of_mem_orthogonal (hinv t ht) hz
  have hor := V.inner_right_of_mem_orthogonal (hinv y hy) hSz
  have hyb : ‖S y‖ ≤ ε := by
    have hy₁ := V.norm_starProjection_apply_le x
    rw [hx] at hy₁
    exact (hband y hy).trans ((mul_le_mul_of_nonneg_left hy₁ hε).trans_eq (mul_one _))
  have hzb := (S.le_opNorm z).trans (mul_le_mul_of_nonneg_right hglobal (norm_nonneg _))
  calc
    ‖S x‖ ^ 2 = ‖S (y + z)‖ ^ 2 := congrArg (fun t => ‖S t‖ ^ 2) hsum.symm
    _ = ‖S y‖ ^ 2 + ‖S z‖ ^ 2 := by
      rw [map_add]
      simpa only [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hor
    _ ≤ ε ^ 2 + (A * ‖z‖) ^ 2 :=
      add_le_add (pow_le_pow_left₀ (norm_nonneg _) hyb _) (pow_le_pow_left₀ (norm_nonneg _) hzb _)
    _ = ε ^ 2 + A ^ 2 * outsideMass V x := by rw [mul_pow]; rfl

/-- The actual compression of an ambient weight to a finite-dimensional cut. -/
def compressedWeight (P : Submodule ℂ H) [FiniteDimensional ℂ P] (W : H →L[ℂ] H) : P →L[ℂ] P :=
  P.orthogonalProjection ∘L W ∘L P.subtypeL

private theorem diagonal_mono {U W : H →L[ℂ] H} (h : U ≤ W) (x : H) :
    (⟪x, U x⟫_ℂ).re ≤ (⟪x, W x⟫_ℂ).re := by
  have hr := ((ContinuousLinearMap.le_def _ _).mp h).re_inner_nonneg_right x
  change 0 ≤ (⟪x, W x - U x⟫_ℂ).re at hr
  simpa [inner_sub_right] using hr

/-- Choose the eigenbasis of the compressed weight. Its eigenvalues are in [c,1], even if
the ambient weight fails to preserve the cut. -/
theorem compressed_weight_eigenbasis (P : Submodule ℂ H) [FiniteDimensional ℂ P] (W : H →L[ℂ] H)
    {n : ℕ} (hn : Module.finrank ℂ P = n) {c : ℝ} (hc : 0 < c)
    (hlo : (c : ℂ) • (1 : H →L[ℂ] H) ≤ W) (hhi : W ≤ 1) :
    ∃ (b : OrthonormalBasis (Fin n) ℂ P) (w : Fin n → ℝ),
      (∀ i, compressedWeight P W (b i) = (w i : ℂ) • b i) ∧ ∀ i, c ≤ w i ∧ w i ≤ 1 := by
  have hpos : W.IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive W).mp <| le_trans
    ((ContinuousLinearMap.nonneg_iff_isPositive _).mpr
      (ContinuousLinearMap.isPositive_one.smul_of_nonneg (by exact_mod_cast hc.le))) hlo
  have hsym := (hpos.orthogonalProjection_comp P).toLinearMap.isSymmetric
  let b := hsym.eigenvectorBasis hn
  let w := hsym.eigenvalues hn
  have heig (i : Fin n) : compressedWeight P W (b i) = (w i : ℂ) • b i :=
    hsym.apply_eigenvectorBasis hn i
  refine ⟨b, w, heig, fun i => ?_⟩
  have hd : (⟪(b i : H), W (b i)⟫_ℂ).re = w i := by
    rw [← P.inner_orthogonalProjection_eq_of_mem_left (b i)]
    change (⟪b i, compressedWeight P W (b i)⟫_ℂ).re = _
    rw [heig, inner_smul_right, b.inner_eq_one]
    simp
  have hl := diagonal_mono hlo (b i : H)
  have hh := diagonal_mono hhi (b i : H)
  change (⟪(b i : H), (c : ℂ) • (b i : H)⟫_ℂ).re ≤ _ at hl
  have hnorm : ‖(b i : H)‖ = 1 := b.norm_eq_one i
  rw [inner_smul_right, inner_self_eq_norm_sq_to_K, hnorm, hd] at hl
  change _ ≤ (⟪(b i : H), (b i : H)⟫_ℂ).re at hh
  rw [hd, inner_self_eq_norm_sq_to_K, hnorm] at hh
  exact ⟨by simpa using hl, by simpa using hh⟩

/-- The numerator is the ordinary finite trace of the product of the compressed weight
and the compressed squared area deviation. -/
def normalizedMoment (P : Submodule ℂ H) [FiniteDimensional ℂ P] (W S : H →L[ℂ] H) : ℝ :=
  let R := S ∘L P.subtypeL
  (LinearMap.trace ℂ P (R.adjoint ∘L R ∘L compressedWeight P W).toLinearMap).re /
    (LinearMap.trace ℂ P (compressedWeight P W).toLinearMap).re

/-- Diagonalizing the weight alone recovers the exact normalized trace moment. -/
theorem normalizedMoment_eq_eigen_sum (P : Submodule ℂ H) [FiniteDimensional ℂ P]
    (W S : H →L[ℂ] H) {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ P) (w : Fin n → ℝ)
    (heig : ∀ i, compressedWeight P W (b i) = (w i : ℂ) • b i) :
    normalizedMoment P W S = (∑ i, w i * ‖S (b i)‖ ^ 2) / (∑ i, w i) := by
  let R := S ∘L P.subtypeL
  change (LinearMap.trace ℂ P (R.adjoint ∘L R ∘L compressedWeight P W).toLinearMap).re /
    (LinearMap.trace ℂ P (compressedWeight P W).toLinearMap).re = _
  rw [LinearMap.trace_eq_sum_inner _ b, LinearMap.trace_eq_sum_inner _ b, Complex.re_sum, Complex.re_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    change (⟪b i, R.adjoint (R (compressedWeight P W (b i)))⟫_ℂ).re = _
    rw [ContinuousLinearMap.adjoint_inner_right, heig, map_smul, inner_smul_right]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact congrArg (fun t : ℝ => w i * t)
      (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) (R (b i))).symm
  · apply Finset.sum_congr rfl
    intro i _
    change (⟪b i, compressedWeight P W (b i)⟫_ℂ).re = _
    rw [heig, inner_smul_right, b.inner_eq_one]
    simp

/-- A genuine finite subspace containing E with controlled normalized trace of the squared
centered area operator. No commutation of the cut projection with W or S is assumed. -/
theorem exists_cut_operator_moment (E V : Submodule ℂ H) [FiniteDimensional ℂ E] [CompleteSpace V]
    (hV : ¬ FiniteDimensional ℂ V) (n : ℕ) (hn : 0 < n) (W S : H →L[ℂ] H) {c ε A : ℝ}
    (hc : 0 < c) (hlo : (c : ℂ) • (1 : H →L[ℂ] H) ≤ W) (hhi : W ≤ 1)
    (hS : S.toLinearMap.IsSymmetric) (hinv : ∀ x ∈ V, S x ∈ V) (hε : 0 ≤ ε)
    (hband : ∀ x ∈ V, ‖S x‖ ≤ ε * ‖x‖) (hglobal : ‖S‖ ≤ A) :
    ∃ (P : Submodule ℂ H) (_ : FiniteDimensional ℂ P), E ≤ P ∧
      Module.finrank ℂ P = Module.finrank ℂ E + n ∧
      normalizedMoment P W S ≤ ε ^ 2 +
        A ^ 2 * Module.finrank ℂ E / (c * ((Module.finrank ℂ E + n : ℕ) : ℝ)) := by
  obtain ⟨e, he, hE, hdim, _, hmoment⟩ := exists_cut_fraction_and_moment E V hV n hn
    (fun x => ‖S x‖ ^ 2) hc (spread_le_of_invariant_band V S hS hinv hε hband hglobal)
  let P := Submodule.span ℂ (Set.range e)
  letI : FiniteDimensional ℂ P := FiniteDimensional.span_of_finite ℂ (Set.finite_range e)
  obtain ⟨b, w, heig, hw⟩ := compressed_weight_eigenbasis P W hdim hc hlo hhi
  exact ⟨P, inferInstance, hE, hdim, (normalizedMoment_eq_eigen_sum P W S b w heig).le.trans
    (hmoment b w hw)⟩

/-- Dilute the old cut by as many band states as needed for a prescribed rank
and tolerance `1/m`. The same cut realizes both requirements. -/
theorem exists_high_rank_operator_cut (E V : Submodule ℂ H) [FiniteDimensional ℂ E] [CompleteSpace V]
    (hV : ¬ FiniteDimensional ℂ V) (N m : ℕ) (hm : 0 < m) (W S : H →L[ℂ] H) {c ε A : ℝ}
    (hc : 0 < c) (hlo : (c : ℂ) • (1 : H →L[ℂ] H) ≤ W) (hhi : W ≤ 1)
    (hS : S.toLinearMap.IsSymmetric) (hinv : ∀ x ∈ V, S x ∈ V) (hε : 0 ≤ ε)
    (hband : ∀ x ∈ V, ‖S x‖ ≤ ε * ‖x‖) (hglobal : ‖S‖ ≤ A) :
    ∃ (P : Submodule ℂ H) (_ : FiniteDimensional ℂ P), E ≤ P ∧ N ≤ Module.finrank ℂ P ∧
      normalizedMoment P W S ≤ ε ^ 2 + A ^ 2 / ((m : ℝ) * c) := by
  let k := Module.finrank ℂ E
  let n := N + m * k + 1
  have hn : 0 < n := by dsimp [n]; omega
  obtain ⟨P, hP, hE, hdim, hq⟩ :=
    exists_cut_operator_moment E V hV n hn W S hc hlo hhi hS hinv hε hband hglobal
  have hNk : N ≤ k + n := by dsimp [n]; omega
  have hkm : k * m ≤ k + n := by dsimp [n]; rw [Nat.mul_comm k m]; omega
  have hkm' : (k : ℝ) * m ≤ ((k + n : ℕ) : ℝ) := by exact_mod_cast hkm
  refine ⟨P, hP, hE, hdim ▸ hNk, hq.trans (add_le_add_left ?_ _)⟩
  change A ^ 2 * k / (c * ((k + n : ℕ) : ℝ)) ≤ A ^ 2 / ((m : ℝ) * c)
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith only [mul_le_mul_of_nonneg_left hkm' (show 0 ≤ A ^ 2 * c by positivity)]

/-- End-to-end finite dimension without a hypothesis selecting high-rank small-response
cuts. The closure lower bound is independently required on all qualifying extensions
of one fixed old finite cut. The observables S_j are the centered area operators. -/
theorem finiteDimensional_of_band_cover_and_closing {ι : Type*} [Finite ι]
    (V : ι → Submodule ℂ H) [∀ j, CompleteSpace (V j)] (hcover : (⨆ j, V j).topologicalClosure = ⊤)
    (W : H →L[ℂ] H) (S : ι → H →L[ℂ] H) (D : Submodule ℂ H → ℝ) {c δ K ε A : ℝ}
    (hc : 0 < c) (hδ : 0 < δ) (hK : 0 ≤ K) (hε : 0 ≤ ε) (m : ℕ) (hm : 0 < m)
    (hparam : K * Real.sqrt (ε ^ 2 + A ^ 2 / ((m : ℝ) * c)) ≤ δ / 4)
    (hlo : (c : ℂ) • (1 : H →L[ℂ] H) ≤ W) (hhi : W ≤ 1)
    (hS : ∀ j, (S j).toLinearMap.IsSymmetric) (hinv : ∀ j x, x ∈ V j → S j x ∈ V j)
    (hband : ∀ j x, x ∈ V j → ‖S j x‖ ≤ ε * ‖x‖) (hglobal : ∀ j, ‖S j‖ ≤ A)
    (hresp : ∀ j (P : Submodule ℂ H) [FiniteDimensional ℂ P], 0 < Module.finrank ℂ P →
      |D P| ≤ K * Real.sqrt (normalizedMoment P W (S j)))
    (E : Submodule ℂ H) [FiniteDimensional ℂ E] (L : ℝ)
    (hlower : ∀ (P : Submodule ℂ H) [FiniteDimensional ℂ P], E ≤ P → 0 < Module.finrank ℂ P →
      |D P| ≤ δ / 4 →
      L ≤ signedClosure (LinearMap.trace ℂ P (compressedWeight P W).toLinearMap).re (D P) δ) :
    FiniteDimensional ℂ H := by
  by_contra hH
  obtain ⟨j, hj⟩ := exists_infinite_band V hcover hH
  have hcoef : 0 < c * δ / 4 := by positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (-L / (c * δ / 4))
  obtain ⟨P, hP, hE, hr, hq⟩ := exists_high_rank_operator_cut E (V j) hj (N + 1) m hm
    W (S j) hc hlo hhi (hS j) (hinv j) hε (hband j) (hglobal j)
  have hPr : 0 < Module.finrank ℂ P := by omega
  have hd := (hresp j P hPr).trans ((mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hq) hK).trans hparam)
  let b := stdOrthonormalBasis ℂ P
  have hT := cutWeight_ge_rank W hlo (b.orthonormal.comp_linearIsometry P.subtypeₗᵢ)
  change c * (Module.finrank ℂ P : ℝ) ≤ cutWeight W (fun i => (b i : H)) at hT
  rw [cutWeight_eq_trace_compression W P b] at hT
  have hZ := (hlower P hE hPr hd).trans (signedClosure_le_neg_rank _ hc hδ hT hd)
  have hNr : (N : ℝ) ≤ Module.finrank ℂ P := by exact_mod_cast (show N ≤ Module.finrank ℂ P by omega)
  have hlarge := (div_lt_iff₀ hcoef).mp (hN.trans_le hNr)
  linarith

#print axioms exists_infinite_band
#print axioms exists_band_extension
#print axioms exists_diluted_cut
#print axioms outside_sum_basis_independent
#print axioms weighted_moment_le
#print axioms exists_cut_fraction_and_moment
#print axioms spread_le_of_invariant_band
#print axioms compressed_weight_eigenbasis
#print axioms normalizedMoment_eq_eigen_sum
#print axioms exists_cut_operator_moment
#print axioms exists_high_rank_operator_cut
#print axioms finiteDimensional_of_band_cover_and_closing

end NullCone.Dilution
