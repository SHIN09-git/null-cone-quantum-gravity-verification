import NullCone.Trace
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Hilbert–Schmidt operators and finite-norm two-boundary coefficients

For a bounded map between arbitrary complete complex Hilbert spaces, the ordinary
extended positive trace of `C.adjoint ∘L C` is the basis-independent sum of the
squared column norms. The coordinates on the full two-boundary Hilbert space are
ordered (output basis, conjugate input basis). The input basis labels contribute
the columns of the matrix of `C`.
-/

noncomputable section

open scoped BigOperators ENNReal InnerProductSpace

namespace NullCone.HilbertSchmidt

open NullCone.Trace

variable {H K ι κ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

private theorem parseval_extended (b : HilbertBasis ι ℂ H) (x : H) :
    (∑' i, ENNReal.ofReal (‖⟪b i, x⟫_ℂ‖ ^ 2)) = ENNReal.ofReal (‖x‖ ^ 2) := by
  have h : HasSum (fun i => ‖⟪b i, x⟫_ℂ‖ ^ 2) (‖x‖ ^ 2) := by
    simpa [HilbertBasis.repr_apply_apply] using
      (lp.hasSum_norm (show 0 < (2 : ℝ≥0∞).toReal by norm_num) (b.repr x))
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) h.summable, h.tsum_eq]

variable [CompleteSpace H] [CompleteSpace K]

private theorem columns_eq_adjoint_columns (b : HilbertBasis ι ℂ H) (d : HilbertBasis κ ℂ K)
    (C : H →L[ℂ] K) :
    (∑' i, ENNReal.ofReal (‖C (b i)‖ ^ 2)) =
      ∑' j, ENNReal.ofReal (‖C.adjoint (d j)‖ ^ 2) := by
  calc
    _ = ∑' i, ∑' j, ENNReal.ofReal (‖⟪d j, C (b i)⟫_ℂ‖ ^ 2) :=
      tsum_congr fun i => (parseval_extended d _).symm
    _ = ∑' j, ∑' i, ENNReal.ofReal (‖⟪d j, C (b i)⟫_ℂ‖ ^ 2) := ENNReal.tsum_comm
    _ = _ := by
      apply tsum_congr
      intro j
      calc
        _ = ∑' i, ENNReal.ofReal (‖⟪b i, C.adjoint (d j)⟫_ℂ‖ ^ 2) := by
          apply tsum_congr
          intro i
          rw [← C.adjoint_inner_left, norm_inner_symm]
        _ = _ := parseval_extended b _

/-- Equality holds in extended nonnegative reals even when the column sum is infinite. -/
theorem column_sum_basis_independent {ι' : Type*} (a : HilbertBasis ι ℂ H)
    (b : HilbertBasis ι' ℂ H) (C : H →L[ℂ] K) :
    (∑' i, ENNReal.ofReal (‖C (a i)‖ ^ 2)) = ∑' j, ENNReal.ofReal (‖C (b j)‖ ^ 2) := by
  obtain ⟨_, d, _⟩ := exists_hilbertBasis ℂ K
  exact (columns_eq_adjoint_columns a d C).trans (columns_eq_adjoint_columns b d C).symm

private theorem extended_cut (C : H →L[ℂ] K) {n : ℕ} (e : Fin n → H) :
    ENNReal.ofReal (cutWeight (C.adjoint ∘L C) e) =
      ∑ i, ENNReal.ofReal (‖C (e i)‖ ^ 2) := by
  rw [cutWeight_adjoint_comp_self]
  exact ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _)

/-- Ordinary positive trace of the Gram operator, on an arbitrary complete basis. -/
theorem positiveTrace_gram_eq_column_sum (b : HilbertBasis ι ℂ H) (C : H →L[ℂ] K) :
    positiveTrace (C.adjoint ∘L C) = ∑' i, ENNReal.ofReal (‖C (b i)‖ ^ 2) := by
  classical
  apply le_antisymm
  · refine iSup_le fun n => iSup_le fun e => iSup_le fun he => ?_
    obtain ⟨u, d, hu, hd⟩ := he.toSubtypeRange.exists_hilbertBasis_extension
    let j : Fin n ↪ u :=
      ⟨fun i => ⟨e i, hu ⟨i, rfl⟩⟩,
        fun i k h => he.linearIndependent.injective (congrArg Subtype.val h)⟩
    rw [extended_cut, ← column_sum_basis_independent d b C]
    calc
      _ = ∑' i : Fin n, ENNReal.ofReal (‖C (d (j i))‖ ^ 2) := by
        rw [tsum_fintype]
        simp [hd, j]
      _ ≤ _ := ENNReal.tsum_comp_le_tsum_of_injective j.injective _
  · rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun s => ?_
    let f : Fin s.card ≃ s := s.equivFin.symm
    let e : Fin s.card → H := fun i => b (f i)
    have he : Orthonormal ℂ e := b.orthonormal.comp (fun i => ((f i : s) : ι))
      (Subtype.val_injective.comp f.injective)
    have hcut := cutWeight_le_positiveTrace (C.adjoint ∘L C) he
    rw [extended_cut] at hcut
    convert hcut using 1
    rw [← Finset.sum_coe_sort s]
    exact (Equiv.sum_comp f (fun i : s => ENNReal.ofReal (‖C (b (i : ι))‖ ^ 2))).symm

private theorem extended_sq_finite_iff {μ E : Type*} [SeminormedAddCommGroup E] (f : μ → E) :
    (∑' i, ENNReal.ofReal (‖f i‖ ^ 2)) ≠ ∞ ↔ Summable (fun i => ‖f i‖ ^ 2) := by
  refine ⟨fun h => ?_, fun h => h.tsum_ofReal_ne_top⟩
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using ENNReal.summable_toReal h

/-- Hilbert–Schmidt criterion on an arbitrary Hilbert basis, without a lower bound on C. -/
theorem finite_trace_iff_hilbertSchmidt (b : HilbertBasis ι ℂ H) (C : H →L[ℂ] K) :
    positiveTrace (C.adjoint ∘L C) ≠ ∞ ↔ Summable (fun i => ‖C (b i)‖ ^ 2) := by
  rw [positiveTrace_gram_eq_column_sum b C]
  exact extended_sq_finite_iff _

/-- The two basis labels give the trace as a single sum over the full product. -/
theorem positiveTrace_gram_eq_matrix_sum (b : HilbertBasis ι ℂ H) (d : HilbertBasis κ ℂ K)
    (C : H →L[ℂ] K) :
    positiveTrace (C.adjoint ∘L C) =
      ∑' p : κ × ι, ENNReal.ofReal (‖⟪d p.1, C (b p.2)⟫_ℂ‖ ^ 2) := by
  rw [positiveTrace_gram_eq_column_sum b C, ENNReal.tsum_prod', ENNReal.tsum_comm]
  exact tsum_congr fun i => (parseval_extended d _).symm

/-- The full coefficient vector in the Hilbert tensor product, in product-basis coordinates. -/
def HasMatrixVector (b : HilbertBasis ι ℂ H) (d : HilbertBasis κ ℂ K) (C : H →L[ℂ] K) : Prop :=
  ∃ v : ℓ²(κ × ι, ℂ), ∀ p, v p = ⟪d p.1, C (b p.2)⟫_ℂ

theorem finite_trace_iff_matrix_vector (b : HilbertBasis ι ℂ H) (d : HilbertBasis κ ℂ K)
    (C : H →L[ℂ] K) : positiveTrace (C.adjoint ∘L C) ≠ ∞ ↔ HasMatrixVector b d C := by
  rw [positiveTrace_gram_eq_matrix_sum b d C, extended_sq_finite_iff]
  have hp : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  constructor
  · intro h
    exact ⟨⟨_, (memℓp_gen_iff hp).2 (by simpa using h)⟩, fun _ => rfl⟩
  · rintro ⟨v, hv⟩
    simpa [hv] using (lp.memℓp v).summable hp

/-- A strict lower bound on the Gram operator makes finite dimension equivalent
to existence of its preparation's finite-norm matrix vector. -/
theorem finiteDimensional_iff_matrix_vector_of_lower (b : HilbertBasis ι ℂ H)
    (d : HilbertBasis κ ℂ K) (C : H →L[ℂ] K) {c : ℝ} (hc : 0 < c)
    (hC : (c : ℂ) • (1 : H →L[ℂ] H) ≤ C.adjoint ∘L C) :
    FiniteDimensional ℂ H ↔ HasMatrixVector b d C :=
  (positiveTrace_ne_top_iff_finiteDimensional _ hc hC).symm.trans
    (finite_trace_iff_matrix_vector b d C)

/-- For the actual matrix vector the trace equals its squared Hilbert norm. -/
theorem positiveTrace_eq_vector_norm_sq (b : HilbertBasis ι ℂ H) (d : HilbertBasis κ ℂ K)
    (C : H →L[ℂ] K) (v : ℓ²(κ × ι, ℂ)) (hv : ∀ p, v p = ⟪d p.1, C (b p.2)⟫_ℂ) :
    positiveTrace (C.adjoint ∘L C) = ENNReal.ofReal (‖v‖ ^ 2) := by
  rw [positiveTrace_gram_eq_matrix_sum b d C]
  simp_rw [← hv]
  have h : HasSum (fun i => ‖v i‖ ^ 2) (‖v‖ ^ 2) := by
    simpa using (lp.hasSum_norm (show 0 < (2 : ℝ≥0∞).toReal by norm_num) v)
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) h.summable, h.tsum_eq]

omit [CompleteSpace H] [CompleteSpace K] in
private theorem operator_zero_of_matrix_zero (b : HilbertBasis ι ℂ H) (d : HilbertBasis κ ℂ K)
    (C : H →L[ℂ] K) (h : ∀ j i, ⟪d j, C (b i)⟫_ℂ = 0) : C = 0 := by
  have hz (i : ι) : C (b i) = 0 := by
    apply d.repr.injective
    apply lp.ext
    funext j
    simpa [d.repr_apply_apply] using h j i
  ext x
  have hs : HasSum (fun _ : ι => (0 : K)) (C x) := by
    simpa [hz] using (b.hasSum_repr x).mapL C
  exact hs.unique hasSum_zero

/-- For a nonzero preparation, finite trace is exactly the existence of a
unit vector whose entries reproduce the matrix after multiplication by a positive scale. -/
theorem normalized_matrix_iff (b : HilbertBasis ι ℂ H) (d : HilbertBasis κ ℂ K)
    (C : H →L[ℂ] K) :
    (∃ (r : ℝ) (u : ℓ²(κ × ι, ℂ)), 0 < r ∧ ‖u‖ = 1 ∧
      ∀ p, (r : ℂ) * u p = ⟪d p.1, C (b p.2)⟫_ℂ) ↔
      C ≠ 0 ∧ positiveTrace (C.adjoint ∘L C) ≠ ∞ := by
  constructor
  · rintro ⟨r, u, hr, hu, hm⟩
    refine ⟨?_, (finite_trace_iff_matrix_vector b d C).2 ⟨(r : ℂ) • u, hm⟩⟩
    intro hC
    have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have hu' : u = 0 := by
      apply lp.ext
      funext p
      have h := hm p
      rw [hC] at h
      simpa [hr'] using h
    simp [hu'] at hu
  · rintro ⟨hC, ht⟩
    obtain ⟨v, hv⟩ := (finite_trace_iff_matrix_vector b d C).1 ht
    have hv' : v ≠ 0 := by
      intro h0
      apply hC
      apply operator_zero_of_matrix_zero b d C
      intro j i
      simpa [h0] using (hv (j, i)).symm
    have hn := norm_pos_iff.mpr hv'
    have hn' : (‖v‖ : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    refine ⟨‖v‖, (‖v‖ : ℂ)⁻¹ • v, hn, ?_, fun p => ?_⟩
    · simp [norm_smul, hn.ne']
    · change (‖v‖ : ℂ) * ((‖v‖ : ℂ)⁻¹ * v p) = _
      rw [← mul_assoc, mul_inv_cancel₀ hn', one_mul, hv]

#print axioms column_sum_basis_independent
#print axioms positiveTrace_gram_eq_column_sum
#print axioms finite_trace_iff_hilbertSchmidt
#print axioms positiveTrace_gram_eq_matrix_sum
#print axioms finite_trace_iff_matrix_vector
#print axioms finiteDimensional_iff_matrix_vector_of_lower
#print axioms positiveTrace_eq_vector_norm_sq
#print axioms normalized_matrix_iff

end NullCone.HilbertSchmidt

