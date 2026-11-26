import Mathlib

noncomputable section
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

namespace NullCone.Model

abbrev H (ι : Type*) := ℓ²(ι, ℂ)

private theorem two_pos : 0 < (2 : ENNReal).toReal := by norm_num

/-- A bounded coordinate multiplier, constructed on the full Hilbert space. -/
def diagVec {ι : Type*} (a : ι → ℂ) (ha : ∀ i, ‖a i‖ ≤ 1) (x : H ι) : H ι :=
  ⟨fun i => a i * x i, (memℓp_gen_iff two_pos).2 <|
    ((lp.memℓp x).summable two_pos).of_nonneg_of_le
      (fun i => Real.rpow_nonneg (norm_nonneg _) _)
      (fun i => Real.rpow_le_rpow (norm_nonneg _) (by
        rw [norm_mul]; simpa using mul_le_mul_of_nonneg_right (ha i) (norm_nonneg (x i)))
        two_pos.le)⟩

def diag {ι : Type*} (a : ι → ℂ) (ha : ∀ i, ‖a i‖ ≤ 1) : H ι →L[ℂ] H ι :=
  LinearMap.mkContinuous
    ({ toFun := diagVec a ha
       map_add' := fun x y => lp.ext (funext fun i => mul_add (a i) (x i) (y i))
       map_smul' := fun c x => lp.ext (funext fun i => by
         change a i * (c * x i) = c * (a i * x i); ring) } : H ι →ₗ[ℂ] H ι) 1
    (fun x => by
      rw [one_mul]
      apply lp.norm_le_of_forall_sum_le two_pos (norm_nonneg _)
      intro s
      refine (Finset.sum_le_sum fun i _ => ?_).trans (lp.sum_rpow_le_norm_rpow two_pos x s)
      apply Real.rpow_le_rpow (norm_nonneg _) _ two_pos.le
      change ‖a i * x i‖ ≤ ‖x i‖
      rw [norm_mul]; simpa using mul_le_mul_of_nonneg_right (ha i) (norm_nonneg (x i)))

@[simp] theorem diag_apply {ι : Type*} (a : ι → ℂ) (ha) (x : H ι) (i : ι) :
    diag a ha x i = a i * x i := rfl

def permVec {ι : Type*} (e : Equiv.Perm ι) (x : H ι) : H ι :=
  ⟨fun i => x (e i), (memℓp_gen_iff two_pos).2 <|
    e.summable_iff.2 ((lp.memℓp x).summable two_pos)⟩

def perm {ι : Type*} (e : Equiv.Perm ι) : H ι ≃ₗᵢ[ℂ] H ι where
  toFun := permVec e
  invFun := permVec e.symm
  left_inv x := lp.ext (funext fun i => by simp [permVec])
  right_inv x := lp.ext (funext fun i => by simp [permVec])
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' x := by
    rw [lp.norm_eq_tsum_rpow two_pos, lp.norm_eq_tsum_rpow two_pos]
    exact congrArg (fun y : ℝ => y ^ (1 / (2 : ENNReal).toReal))
      (e.tsum_eq (fun i => ‖x i‖ ^ (2 : ENNReal).toReal))

@[simp] theorem perm_apply {ι : Type*} (e : Equiv.Perm ι) (x : H ι) (i : ι) :
    perm e x i = x (e i) := rfl

def ket {ι : Type*} [DecidableEq ι] (i : ι) : H ι := lp.single 2 i 1

theorem ket_inner {ι : Type*} [DecidableEq ι] (i : ι) (x : H ι) :
    inner ℂ (ket i) x = x i := by simp [ket, lp.inner_single_left, RCLike.inner_apply]

def proj {ι : Type*} [DecidableEq ι] (s : Finset ι) : H ι →L[ℂ] H ι :=
  diag (fun i => if i ∈ s then 1 else 0) (fun i => by by_cases h : i ∈ s <;> simp [h])

@[simp] theorem proj_apply {ι : Type*} [DecidableEq ι] (s : Finset ι) (x : H ι) (i : ι) :
    proj s x i = if i ∈ s then x i else 0 := by by_cases h : i ∈ s <;> simp [proj, h]

theorem proj_idem {ι : Type*} [DecidableEq ι] (s : Finset ι) (x : H ι) :
    proj s (proj s x) = proj s x := by
  apply lp.ext; funext i; by_cases h : i ∈ s <;> simp [h]

theorem proj_symmetric {ι : Type*} [DecidableEq ι] (s : Finset ι) (x y : H ι) :
    inner ℂ (proj s x) y = inner ℂ x (proj s y) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]; apply tsum_congr; intro i
  by_cases h : i ∈ s <;> simp [h]

theorem proj_eq_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (x : H ι) :
    proj s x = ∑ i ∈ s, lp.single 2 i (x i) := by
  apply lp.ext; funext j
  simp only [proj_apply, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single, Pi.single_apply]
  by_cases h : j ∈ s <;> simp [h]

theorem proj_strong_of_cofinal {ι : Type*} [DecidableEq ι] {s : ℕ → Finset ι}
    (hs : Tendsto s atTop atTop) (x : H ι) :
    Tendsto (fun k => proj (s k) x) atTop (𝓝 x) := by
  simp_rw [proj_eq_sum]; exact (lp.hasSum_single ENNReal.ofNat_ne_top x).comp hs

end NullCone.Model

