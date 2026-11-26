import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Tactic

/-!
# Open matrix elements and positive closed traces

The extended positive trace is defined using all finite orthonormal families.
The signed estimates keep the geometric weight and the normalized response separate.
-/

noncomputable section

open scoped BigOperators ENNReal InnerProductSpace Topology
open Filter

namespace NullCone.Trace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The weight on a cut with the specified finite orthonormal basis. -/
def cutWeight (W : H →L[ℂ] H) {n : ℕ} (e : Fin n → H) : ℝ :=
  ∑ i, (⟪e i, W (e i)⟫_ℂ).re

/-- For positive operators this is the ordinary extended positive trace. -/
def positiveTrace (W : H →L[ℂ] H) : ℝ≥0∞ :=
  ⨆ (n : ℕ) (e : Fin n → H) (_ : Orthonormal ℂ e), ENNReal.ofReal (cutWeight W e)

theorem cutWeight_le_positiveTrace (W : H →L[ℂ] H) {n : ℕ}
    {e : Fin n → H} (he : Orthonormal ℂ e) :
    ENNReal.ofReal (cutWeight W e) ≤ positiveTrace W :=
  le_iSup_of_le n <| le_iSup_of_le e <| le_iSup_of_le he le_rfl

variable [CompleteSpace H]

omit [CompleteSpace H] in
/-- A finite cut equals the ordinary trace of the compression to its range. -/
theorem cutWeight_eq_trace_compression (W : H →L[ℂ] H) (V : Submodule ℂ H)
    [FiniteDimensional ℂ V] {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ V) :
    cutWeight W (fun i => (b i : H)) =
      (LinearMap.trace ℂ V (V.orthogonalProjection ∘L W ∘L V.subtypeL).toLinearMap).re := by
  rw [LinearMap.trace_eq_sum_inner _ b, Complex.re_sum]
  simp only [cutWeight, ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply, Submodule.inner_orthogonalProjection_eq_of_mem_left]

/-- For a preparation operator the weight is the sum of squared image norms. -/
theorem cutWeight_adjoint_comp_self {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (C : H →L[ℂ] K) {n : ℕ} (e : Fin n → H) :
    cutWeight (C.adjoint ∘L C) e = ∑ i, ‖C (e i)‖ ^ 2 := by
  apply Finset.sum_congr rfl
  intro i _
  change (⟪e i, C.adjoint (C (e i))⟫_ℂ).re = _
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) (C (e i))).symm

/-- The finite-rank trace counts at least `c` for each orthonormal vector. -/
theorem cutWeight_ge_rank (W : H →L[ℂ] H) {c : ℝ}
    (hW : (c : ℂ) • (1 : H →L[ℂ] H) ≤ W) {n : ℕ}
    {e : Fin n → H} (he : Orthonormal ℂ e) :
    c * (n : ℝ) ≤ cutWeight W e := by
  calc
    c * (n : ℝ) = ∑ _ : Fin n, c := by simp [mul_comm]
    _ ≤ cutWeight W e := by
      apply Finset.sum_le_sum
      intro i _
      have h := ((ContinuousLinearMap.le_def _ _).mp hW).re_inner_nonneg_right (e i)
      change 0 ≤ (⟪e i, W (e i) - (c : ℂ) • e i⟫_ℂ).re at h
      rw [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, he.norm_eq_one] at h
      simpa [sub_nonneg] using h

/-- In finite dimension the supremum agrees with mathlib's algebraic trace.
Extend each orthonormal family to a basis and use positivity on the complement. -/
theorem positiveTrace_eq_trace [FiniteDimensional ℂ H] (W : H →L[ℂ] H)
    (hW : W.IsPositive) :
    positiveTrace W = ENNReal.ofReal ((LinearMap.trace ℂ H W.toLinearMap).re) := by
  classical
  apply le_antisymm
  · refine iSup_le fun n => iSup_le fun e => iSup_le fun he => ENNReal.ofReal_le_ofReal ?_
    obtain ⟨u, b, hu, hb⟩ := he.toSubtypeRange.exists_orthonormalBasis_extension
    let j : Fin n ↪ u :=
      ⟨fun i => ⟨e i, hu ⟨i, rfl⟩⟩, fun i k h => he.linearIndependent.injective (congrArg Subtype.val h)⟩
    let d : u → ℝ := fun i => (⟪b i, W (b i)⟫_ℂ).re
    have hd (i : Fin n) : d (j i) = (⟪e i, W (e i)⟫_ℂ).re := by
      simp [d, hb, j]
    rw [LinearMap.trace_eq_sum_inner _ b, Complex.re_sum]
    calc
      cutWeight W e = ∑ i ∈ Finset.univ.map j, d i := by simp [cutWeight, hd]
      _ ≤ ∑ i, d i := Finset.sum_le_univ_sum_of_nonneg fun i => hW.re_inner_nonneg_right _
  · let b := stdOrthonormalBasis ℂ H
    rw [LinearMap.trace_eq_sum_inner _ b, Complex.re_sum]
    exact cutWeight_le_positiveTrace W b.orthonormal

/-- An infinite orthonormal family forces the ordinary trace to be infinite
under a positive scalar lower bound. The index type need not be countable. -/
theorem positiveTrace_eq_top_of_infinite_family (W : H →L[ℂ] H) {c : ℝ}
    (hc : 0 < c) (hW : (c : ℂ) • (1 : H →L[ℂ] H) ≤ W)
    {ι : Type*} [Infinite ι] {v : ι → H} (hv : Orthonormal ℂ v) :
    positiveTrace W = ∞ := by
  by_contra hfin
  obtain ⟨n, hn⟩ := exists_nat_gt ((positiveTrace W).toReal / c)
  let j : Fin n → ι := fun i => Infinite.natEmbedding ι i.val
  have hj : Function.Injective j := (Infinite.natEmbedding ι).injective.comp Fin.val_injective
  have he := hv.comp j hj
  have hbound := (ENNReal.ofReal_le_ofReal (cutWeight_ge_rank W hW he)).trans
    (cutWeight_le_positiveTrace W he)
  have hreal := ENNReal.toReal_mono hfin hbound
  rw [ENNReal.toReal_ofReal (mul_nonneg hc.le (Nat.cast_nonneg n))] at hreal
  exact (not_lt_of_ge hreal) (by simpa [mul_comm] using (div_lt_iff₀ hc).mp hn)

/-- Finiteness of the ordinary trace on the full Hilbert space implies finite dimension. -/
theorem finiteDimensional_of_positiveTrace_ne_top (W : H →L[ℂ] H) {c : ℝ}
    (hc : 0 < c) (hW : (c : ℂ) • (1 : H →L[ℂ] H) ≤ W)
    (hfin : positiveTrace W ≠ ∞) : FiniteDimensional ℂ H := by
  classical
  obtain ⟨ι, b, _⟩ := exists_hilbertBasis ℂ H
  rcases finite_or_infinite ι with hι | hι
  · letI := Fintype.ofFinite ι
    exact FiniteDimensional.of_fintype_basis b.toOrthonormalBasis.toBasis
  · exact (hfin (positiveTrace_eq_top_of_infinite_family W hc hW b.orthonormal)).elim

/-- The same coercive operator has finite positive trace exactly in finite dimension. -/
theorem positiveTrace_ne_top_iff_finiteDimensional (W : H →L[ℂ] H) {c : ℝ}
    (hc : 0 < c) (hW : (c : ℂ) • (1 : H →L[ℂ] H) ≤ W) :
    positiveTrace W ≠ ∞ ↔ FiniteDimensional ℂ H := by
  refine ⟨finiteDimensional_of_positiveTrace_ne_top W hc hW, fun _ => ?_⟩
  have hpos : W.IsPositive := by
    apply (ContinuousLinearMap.nonneg_iff_isPositive W).mp
    apply le_trans _ hW
    apply (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
    exact ContinuousLinearMap.isPositive_one.smul_of_nonneg (by exact_mod_cast hc.le)
  rw [positiveTrace_eq_trace W hpos]
  exact ENNReal.ofReal_ne_top

omit [CompleteSpace H] in
/-- Open sewing for any fixed finite-norm states. The norm sum is bounded
by Cauchy-Schwarz, including for Hilbert bases with uncountably many labels. -/
theorem open_matrix_elements {ι : Type*} (b : HilbertBasis ι ℂ H) (x y : H) :
    HasSum (fun i => ⟪y, b i⟫_ℂ * ⟪b i, x⟫_ℂ) ⟪y, x⟫_ℂ ∧
    Summable (fun i => ‖⟪y, b i⟫_ℂ * ⟪b i, x⟫_ℂ‖) ∧
    (∑' i, ‖⟪y, b i⟫_ℂ * ⟪b i, x⟫_ℂ‖) ≤ ‖y‖ * ‖x‖ := by
  refine ⟨b.hasSum_inner_mul_inner y x, ?_⟩
  have h := lp.tsum_mul_le_mul_norm (p := 2) (q := 2)
    (by rw [Real.holderConjugate_iff]; norm_num) (b.repr y) (b.repr x)
  simpa only [norm_mul, norm_inner_symm (𝕜 := ℂ) y, b.repr_apply_apply,
    LinearIsometryEquiv.norm_map] using h

/-- The usual coordinate Hilbert basis of complex square-summable sequences. -/
def sequenceBasis : HilbertBasis ℕ ℂ ℓ²(ℕ, ℂ) :=
  .ofRepr (LinearIsometryEquiv.refl ℂ _)

/-- With identity evolution on ℓ², every fixed-state open amplitude converges
absolutely, while the ordinary positive identity trace equals infinity. -/
theorem l2_open_and_closed :
    (∀ x y : ℓ²(ℕ, ℂ),
      HasSum (fun i => ⟪y, sequenceBasis i⟫_ℂ * ⟪sequenceBasis i, x⟫_ℂ) ⟪y, x⟫_ℂ ∧
      Summable (fun i => ‖⟪y, sequenceBasis i⟫_ℂ * ⟪sequenceBasis i, x⟫_ℂ‖)) ∧
    positiveTrace (1 : ℓ²(ℕ, ℂ) →L[ℂ] ℓ²(ℕ, ℂ)) = ∞ := by
  refine ⟨fun x y => ⟨(open_matrix_elements sequenceBasis x y).1,
    (open_matrix_elements sequenceBasis x y).2.1⟩, ?_⟩
  apply positiveTrace_eq_top_of_infinite_family _ (c := 1) zero_lt_one _ sequenceBasis.orthonormal
  simp

/-- The unnormalized insertion using the same cut for weight and response. -/
def signedClosure (T response δ : ℝ) : ℝ := T * (response - δ / 2)

/-- The strengthened negative bound comes from the normalized response estimate
and the independent positive rank estimate on the weight. -/
theorem signedClosure_le_neg_rank {c δ T response : ℝ} (rank : ℕ)
    (hc : 0 < c) (hδ : 0 < δ) (hT : c * (rank : ℝ) ≤ T)
    (hresponse : |response| ≤ δ / 4) :
    signedClosure T response δ ≤ -(c * δ / 4) * rank := by
  have hT₀ : 0 ≤ T := (mul_nonneg hc.le (Nat.cast_nonneg rank)).trans hT
  have hresp : response - δ / 2 ≤ -(δ / 4) := by linarith [(abs_le.mp hresponse).2]
  calc
    signedClosure T response δ ≤ T * (-(δ / 4)) := mul_le_mul_of_nonneg_left hresp hT₀
    _ ≤ (c * rank) * (-(δ / 4)) := mul_le_mul_of_nonpos_right hT (by linarith)
    _ = -(c * δ / 4) * rank := by ring

/-- Operator version, with the rank estimate for each cut supplied by its actual diagonal sum. -/
theorem signedCut_le_neg_rank (W : H →L[ℂ] H) {c δ response : ℝ}
    (hc : 0 < c) (hδ : 0 < δ) (hW : (c : ℂ) • (1 : H →L[ℂ] H) ≤ W)
    {n : ℕ} {e : Fin n → H} (he : Orthonormal ℂ e) (hresponse : |response| ≤ δ / 4) :
    signedClosure (cutWeight W e) response δ ≤ -(c * δ / 4) * n :=
  signedClosure_le_neg_rank n hc hδ (cutWeight_ge_rank W hW he) hresponse

/-- A single finite lower bound on all signed closures bounds the rank of every cut. -/
theorem rank_bound_of_signed_lower {ι : Type*} (rank : ι → ℕ) (T response : ι → ℝ)
    {c δ L : ℝ} (hc : 0 < c) (hδ : 0 < δ) (hT : ∀ i, c * (rank i : ℝ) ≤ T i)
    (hresponse : ∀ i, |response i| ≤ δ / 4)
    (hL : ∀ i, L ≤ signedClosure (T i) (response i) δ) :
    ∀ i, (rank i : ℝ) ≤ -L / (c * δ / 4) := by
  intro i
  apply (le_div_iff₀ (by positivity : 0 < c * δ / 4)).mpr
  linarith only [(hL i).trans (signedClosure_le_neg_rank _ hc hδ (hT i) (hresponse i))]

/-- Globally unbounded ranks are incompatible with a common finite lower bound. -/
theorem signedClosure_no_uniform_lower {ι : Type*} (rank : ι → ℕ) (T response : ι → ℝ)
    {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) (hrank : ∀ n : ℕ, ∃ i, n ≤ rank i)
    (hT : ∀ i, c * (rank i : ℝ) ≤ T i) (hresponse : ∀ i, |response i| ≤ δ / 4) :
    ¬ ∃ L : ℝ, ∀ i, L ≤ signedClosure (T i) (response i) δ := by
  rintro ⟨L, hL⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (-L / (c * δ / 4))
  obtain ⟨i, hi⟩ := hrank n
  have hni : (n : ℝ) ≤ rank i := by exact_mod_cast hi
  exact (not_lt_of_ge (rank_bound_of_signed_lower rank T response hc hδ hT hresponse hL i))
    (hn.trans_le hni)

/-- Along a rank-exhausting net the signed closures tend to minus infinity. -/
theorem signedClosure_tendsto_atBot {ι : Type*} {l : Filter ι}
    (rank : ι → ℕ) (T response : ι → ℝ) {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (hrank : Tendsto rank l atTop) (hT : ∀ᶠ i in l, c * (rank i : ℝ) ≤ T i)
    (hresponse : ∀ᶠ i in l, |response i| ≤ δ / 4) :
    Tendsto (fun i => signedClosure (T i) (response i) δ) l atBot := by
  have hr : Tendsto (fun i => (rank i : ℝ)) l atTop := tendsto_natCast_atTop_atTop.comp hrank
  have hneg : Tendsto (fun i => -(c * δ / 4) * (rank i : ℝ)) l atBot :=
    hr.const_mul_atTop_of_neg (neg_lt_zero.mpr (by positivity : 0 < c * δ / 4))
  apply tendsto_atBot_mono' _ _ hneg
  filter_upwards [hT, hresponse] with i hi hj
  exact signedClosure_le_neg_rank _ hc hδ hi hj

/-- Cofinal rank unboundedness is enough to exclude a finite limit, even when
the ranks need not tend to infinity. -/
theorem signedClosure_no_finite_limit {ι : Type*} {l : Filter ι}
    (rank : ι → ℕ) (T response : ι → ℝ) {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (hrank : ∀ n : ℕ, ∃ᶠ i in l, n ≤ rank i)
    (hT : ∀ᶠ i in l, c * (rank i : ℝ) ≤ T i)
    (hresponse : ∀ᶠ i in l, |response i| ≤ δ / 4) (a : ℝ) :
    ¬ Tendsto (fun i => signedClosure (T i) (response i) δ) l (𝓝 a) := by
  intro hlim
  let k := c * δ / 4
  have hk : 0 < k := by dsimp [k]; positivity
  obtain ⟨n, hn⟩ := exists_nat_gt ((1 - a) / k)
  have hlow := hlim.eventually (lt_mem_nhds (show a - 1 < a by linarith))
  obtain ⟨i, hi, hTi, hΔi, hLi⟩ := ((hrank n).and_eventually
    (hT.and (hresponse.and hlow))).exists
  have hni : (n : ℝ) ≤ rank i := by exact_mod_cast hi
  have hstrict := (div_lt_iff₀ hk).mp (hn.trans_le hni)
  have hbound : signedClosure (T i) (response i) δ ≤ -k * rank i :=
    signedClosure_le_neg_rank _ hc hδ hTi hΔi
  linarith

#print axioms cutWeight_le_positiveTrace
#print axioms cutWeight_eq_trace_compression
#print axioms cutWeight_adjoint_comp_self
#print axioms cutWeight_ge_rank
#print axioms positiveTrace_eq_trace
#print axioms positiveTrace_eq_top_of_infinite_family
#print axioms finiteDimensional_of_positiveTrace_ne_top
#print axioms positiveTrace_ne_top_iff_finiteDimensional
#print axioms open_matrix_elements
#print axioms l2_open_and_closed
#print axioms signedClosure_le_neg_rank
#print axioms signedCut_le_neg_rank
#print axioms rank_bound_of_signed_lower
#print axioms signedClosure_no_uniform_lower
#print axioms signedClosure_tendsto_atBot
#print axioms signedClosure_no_finite_limit

end NullCone.Trace
