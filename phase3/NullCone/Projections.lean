import NullCone.Model
import NullCone.Trace

noncomputable section
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology
namespace NullCone.Model

theorem ket_orthonormal {ι : Type*} [DecidableEq ι] : Orthonormal ℂ (ket (ι := ι)) := by
  rw [orthonormal_iff_ite]; intro i j
  rw [ket_inner]; simp [ket, Pi.single_apply]

theorem model_infinite : ¬FiniteDimensional ℂ One := by
  intro hf
  exact Module.Finite.not_linearIndependent_of_infinite (R := ℂ) (ket (ι := Label)) ket_orthonormal.linearIndependent

theorem model_open (x y : One) :
    HasSum (fun i : Label => inner ℂ y (ket i) * inner ℂ (ket i) x) (inner ℂ y x) ∧
    Summable (fun i : Label => ‖inner ℂ y (ket i) * inner ℂ (ket i) x‖) := by
  let b : HilbertBasis Label ℂ One := .ofRepr (LinearIsometryEquiv.refl ℂ _)
  have hb (i : Label) : b i = ket i := (b.repr_symm_single i).symm
  obtain ⟨h₁,h₂,_⟩ := NullCone.Trace.open_matrix_elements b x y
  simpa only [hb] using And.intro h₁ h₂

theorem proj_range {ι : Type*} [DecidableEq ι] (s : Finset ι) :
    LinearMap.range (proj s).toLinearMap =
      Submodule.span ℂ (Set.range (fun i : s => ket (i : ι))) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    change proj s x ∈ _
    rw [proj_eq_sum]; apply Submodule.sum_mem; intro i hi
    have he : lp.single (E := fun _ : ι => ℂ) 2 i (x i) = x i • ket i := by
      apply lp.ext; funext j; by_cases h : j = i <;> simp [ket, lp.coeFn_single, h]
    rw [he]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i,hi⟩, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩; refine ⟨ket (i : ι), ?_⟩
    change proj s (ket (i : ι)) = ket (i : ι)
    apply lp.ext; funext j
    by_cases h : j = (i : ι)
    · simp [h,i.property]
    · simp [ket, h]

theorem proj_finite_rank {ι : Type*} [DecidableEq ι] (s : Finset ι) :
    FiniteDimensional ℂ (LinearMap.range (proj s).toLinearMap) ∧
    Module.finrank ℂ (LinearMap.range (proj s).toLinearMap) = s.card := by
  rw [proj_range]; constructor
  · exact FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  · have hi := (ket_orthonormal (ι := ι)).linearIndependent.comp
      (fun j : s => (j : ι)) Subtype.val_injective
    simpa using finrank_span_eq_card hi

theorem proj_selfAdjoint {ι : Type*} [DecidableEq ι] (s : Finset ι) : IsSelfAdjoint (proj s) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (proj_symmetric s)

theorem area_selfAdjoint : IsSelfAdjoint area :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr area_symmetric

theorem observable_selfAdjoint : IsSelfAdjoint observable :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr observable_symmetric

theorem cap_adjoint_cap : cap.adjoint.comp cap = weight := by
  ext x : 1
  apply ext_inner_left ℂ; intro y
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right, cap_weight]

theorem weight_coercive (x : One) : (inner ℂ x (weight x)).re = w * ‖x‖^2 := by
  simp [weight, inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]

theorem rightBoost_unitary : Function.Surjective rightBoost ∧ ∀ v, ‖rightBoost v‖ = ‖v‖ := by
  refine ⟨fun v => ?_, boost_isometry⟩
  let back := diag (fun p : Label × Label => conj (rightPhase p.2)) (fun p => by simp [rightPhase_unit])
  refine ⟨back v, ?_⟩; apply lp.ext; funext p
  simp only [back, rightBoost, diag_apply, ← mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    rightPhase_unit, one_pow, Complex.ofReal_one, one_mul]

def insertion : Two →L[ℂ] Two :=
  rightBoost.adjoint.comp (observable.comp rightBoost) - observable -
  (delta / 2 : ℂ) • ContinuousLinearMap.id ℂ Two

theorem signed_is_matrix_element (s : Finset Label) :
    signed s = (inner ℂ (prepared s) (insertion (prepared s))).re := by
  simp [signed, change, mass, insertion, ContinuousLinearMap.adjoint_inner_right,
    inner_self_eq_norm_sq_to_K, Complex.mul_re]

theorem flip_selfAdjoint : IsSelfAdjoint flip.toContinuousLinearEquiv.toContinuousLinearMap := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  simpa only [flip_involution] using flip.inner_map_map x (flip y)

theorem observable_norm_le_one : ‖observable‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro v
  simp [observable]

theorem insertion_selfAdjoint : IsSelfAdjoint insertion := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  change inner ℂ (insertion x) y = inner ℂ x (insertion y)
  simp only [insertion, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right, ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_right, observable_symmetric]
  simp [map_ofNat]

end NullCone.Model

