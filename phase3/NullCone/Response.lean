import NullCone.Hilbert

/-!
# Area spread and the response to a right boundary boost, (5.32) and (D.23)

The two-boundary space has arbitrary left and right label sets. The area is
diagonal on the right label. The vector can have off-diagonal coefficients,
and its left and right labels can be correlated.
-/

noncomputable section

open Complex MeasureTheory
open scoped InnerProductSpace

namespace NullCone.Response

/-- Changing a unit vector changes a bounded operator's expectation by at most this amount. -/
theorem expectation_sub_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (O : E →L[ℂ] E) (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖inner ℂ u (O u) - inner ℂ v (O v)‖ ≤ 2 * ‖O‖ * ‖u - v‖ := by
  have hid : inner ℂ u (O u) - inner ℂ v (O v) =
      inner ℂ (u - v) (O u) + inner ℂ v (O (u - v)) := by
    rw [map_sub, inner_sub_left, inner_sub_right]
    abel
  have h₁ : ‖inner ℂ (u - v) (O u)‖ ≤ ‖u - v‖ * ‖O‖ := by
    apply (norm_inner_le_norm (𝕜 := ℂ) _ _).trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    simpa [hu] using O.le_opNorm u
  have h₂ : ‖inner ℂ v (O (u - v))‖ ≤ ‖O‖ * ‖u - v‖ := by
    apply (norm_inner_le_norm (𝕜 := ℂ) _ _).trans
    rw [hv, one_mul]
    exact O.le_opNorm _
  rw [hid]
  exact (norm_add_le _ _).trans ((add_le_add h₁ h₂).trans_eq (by ring))

def phase (x : ℝ) : ℂ := Complex.exp ((x : ℂ) * I)

@[simp] theorem phase_norm (x : ℝ) : ‖phase x‖ = 1 := Complex.norm_exp_ofReal_mul_I x

/-- A unit-circle chord is bounded by the length of its arc. -/
theorem phase_sub_one_le (x : ℝ) : ‖phase x - 1‖ ≤ |x| := by
  have hd (y : ℝ) : HasDerivAt phase (phase y * I) y := by
    have h : HasDerivAt (fun z : ℝ => (z : ℂ)) 1 y := by
      simpa using (hasDerivAt_id y).ofReal_comp
    simpa [phase] using (h.mul_const I).cexp
  have hb (y : ℝ) (_ : y ∈ (Set.univ : Set ℝ)) : ‖phase y * I‖ ≤ 1 := by simp
  have h := (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun y _ => (hd y).hasDerivWithinAt) hb (Set.mem_univ 0) (Set.mem_univ x)
  simpa [phase, Real.norm_eq_abs] using h

private theorem phase_square_le (t b : ℝ) :
    ‖phase (t * b) - 1‖ ^ 2 ≤ t ^ 2 * b ^ 2 := by
  calc
    _ ≤ |t * b| ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (phase_sub_one_le _) 2
    _ = _ := by rw [sq_abs, mul_pow]

/-- Integrated chord bound for any positive Borel measure on the real spectral axis. -/
theorem integrated_phase_square_le (μ : Measure ℝ) (t s₀ : ℝ)
    (hm : Integrable (fun s : ℝ => (s - s₀) ^ 2) μ) :
    Integrable (fun s : ℝ => ‖phase (t * (s - s₀)) - 1‖ ^ 2) μ ∧
      (∫ s : ℝ, ‖phase (t * (s - s₀)) - 1‖ ^ 2 ∂μ) ≤
        t ^ 2 * ∫ s : ℝ, (s - s₀) ^ 2 ∂μ := by
  have hR := hm.const_mul (t ^ 2)
  have hc : Continuous (fun s : ℝ => ‖phase (t * (s - s₀)) - 1‖ ^ 2) := by
    unfold phase
    fun_prop
  have hL := hR.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall fun s => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact phase_square_le t (s - s₀))
  refine ⟨hL, ?_⟩
  rw [← integral_const_mul]
  exact integral_mono hL hR (fun s => phase_square_le t (s - s₀))

section RightBoundary

variable {α β : Type*}

/-- The centered right boost multiplies each coefficient by the phase of its right area. -/
def rightBoost (area : β → ℝ) (t s₀ : ℝ) : Model.H (α × β) →L[ℂ] Model.H (α × β) :=
  Model.diag (fun p : α × β => phase (t * (area p.2 - s₀))) (fun _ => (phase_norm _).le)

@[simp] theorem rightBoost_apply (area : β → ℝ) (t s₀ : ℝ) (ψ : Model.H (α × β)) (p : α × β) :
    rightBoost area t s₀ ψ p = phase (t * (area p.2 - s₀)) * ψ p := rfl

theorem rightBoost_norm (area : β → ℝ) (t s₀ : ℝ) (ψ : Model.H (α × β)) :
    ‖rightBoost area t s₀ ψ‖ = ‖ψ‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ENNReal).toReal),
    lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ENNReal).toReal)]
  simp

/-- Contribution of one two-boundary coefficient to the second moment about `s₀`. -/
def momentTerm (area : β → ℝ) (s₀ : ℝ) (ψ : Model.H (α × β)) (p : α × β) : ℝ :=
  ‖ψ p‖ ^ 2 * (area p.2 - s₀) ^ 2

def secondMoment (area : β → ℝ) (s₀ : ℝ) (ψ : Model.H (α × β)) : ℝ :=
  ∑' p, momentTerm area s₀ ψ p

private theorem square_hasSum {ι : Type*} (v : Model.H ι) :
    HasSum (fun i => ‖v i‖ ^ 2) (‖v‖ ^ 2) := by
  simpa using lp.hasSum_norm (p := 2) (by norm_num) v

/-- (D.23) in a right-area eigenbasis. Only the state's second moment must be finite. -/
theorem boost_distance_sq_le (area : β → ℝ) (t s₀ : ℝ) (ψ : Model.H (α × β))
    (hm : Summable (momentTerm area s₀ ψ)) :
    ‖rightBoost area t s₀ ψ - ψ‖ ^ 2 ≤ t ^ 2 * secondMoment area s₀ ψ := by
  have hd := square_hasSum (rightBoost area t s₀ ψ - ψ)
  rw [← hd.tsum_eq, secondMoment, ← tsum_mul_left]
  apply hd.summable.tsum_mono (hm.mul_left _) (fun p => ?_)
  change ‖phase (t * (area p.2 - s₀)) * ψ p - ψ p‖ ^ 2 ≤ _
  rw [← sub_one_mul, norm_mul, mul_pow, momentTerm]
  calc
    _ ≤ (t ^ 2 * (area p.2 - s₀) ^ 2) * ‖ψ p‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (phase_square_le _ _) (sq_nonneg _)
    _ = _ := by ring

/-- Restoring the reference area introduces one global phase, common to all coefficients. -/
theorem rightBoost_uncentered (area : β → ℝ) (t s₀ : ℝ) (ψ : Model.H (α × β)) :
    rightBoost area t 0 ψ = phase (t * s₀) • rightBoost area t s₀ ψ := by
  apply lp.ext
  funext p
  simp only [rightBoost_apply, sub_zero, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, ← mul_assoc]
  have hadd : ∀ x y, phase x * phase y = phase (x + y) := by
    intro x y
    simp [phase, add_mul, Complex.exp_add]
  rw [hadd]
  congr 2
  ring

private theorem expectation_phase {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (O : E →L[ℂ] E) (x : ℝ) (v : E) :
    inner ℂ (phase x • v) (O (phase x • v)) = inner ℂ v (O v) := by
  rw [map_smul, inner_smul_left, inner_smul_right, ← mul_assoc, Complex.conj_mul', phase_norm]
  norm_num

/-- (5.32) for a normalized two-boundary state, with the paper's rapidity parameter.
The expectation uses the uncentered boost; any admissible center bounds the response. -/
theorem boost_response_le (area : β → ℝ) (η s₀ : ℝ) (ψ : Model.H (α × β))
    (O : Model.H (α × β) →L[ℂ] Model.H (α × β))
    (hu : ‖ψ‖ = 1) (hm : Summable (momentTerm area s₀ ψ)) :
    let U := rightBoost (α := α) area (η / (2 * Real.pi)) 0
    ‖inner ℂ (U ψ) (O (U ψ)) - inner ℂ ψ (O ψ)‖ ≤
      |η| / Real.pi * ‖O‖ * Real.sqrt (secondMoment area s₀ ψ) := by
  dsimp only
  let t := η / (2 * Real.pi)
  rw [rightBoost_uncentered area t s₀ ψ, expectation_phase]
  have hdist := Real.sqrt_le_sqrt (boost_distance_sq_le area t s₀ ψ hm)
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs] at hdist
  refine (expectation_sub_le O _ ψ ((rightBoost_norm ..).trans hu) hu).trans ?_
  calc
    _ ≤ (2 * ‖O‖) * (|t| * Real.sqrt (secondMoment area s₀ ψ)) :=
      mul_le_mul_of_nonneg_left hdist (by positivity)
    _ = _ := by
      simp only [t, abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      ring

end RightBoundary

#print axioms expectation_sub_le
#print axioms phase_norm
#print axioms phase_sub_one_le
#print axioms integrated_phase_square_le
#print axioms rightBoost_apply
#print axioms rightBoost_norm
#print axioms boost_distance_sq_le
#print axioms rightBoost_uncentered
#print axioms boost_response_le

end NullCone.Response
