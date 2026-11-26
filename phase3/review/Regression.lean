import NullCone.Limits
import NullCone.Perturbation
import NullCone.Dilution

/-! Independent checks phrased in the quantities used by the v0.2 derivation. -/

set_option warningAsError true
noncomputable section
open NullCone.Model Filter Topology
open scoped InnerProductSpace
namespace SemanticProbe

private def actualZ (r : Route) (k : ℕ) : ℝ :=
  (inner ℂ (prepared (stages r k)) (insertion (prepared (stages r k)))).re

private theorem actual_eq (r : Route) (k : ℕ) : actualZ r k = signed (stages r k) :=
  (signed_is_matrix_element _).symm

theorem five_matrix_element_limits : Tendsto (actualZ Route.balanced) atTop atTop ∧
    Tendsto (actualZ Route.positive) atTop (𝓝 (Real.exp (-3) * (1 - Real.cos 1))) ∧
    Tendsto (actualZ Route.zero) atTop (𝓝 0) ∧
    Tendsto (actualZ Route.negative) atTop (𝓝 (-(Real.exp (-3) * (1 - Real.cos 1)))) ∧
    Tendsto (actualZ Route.dilute) atTop atBot := by
  have heq (r : Route) : actualZ r = fun k => signed (stages r k) := funext (actual_eq r)
  simp only [heq]
  exact ⟨balanced_limit, positive_limit, zero_limit, negative_limit, dilute_limit⟩

theorem no_finite_matrix_element_net_limit (z : ℝ) : ¬ Tendsto (fun s : Finset Label =>
    (inner ℂ (prepared s) (insertion (prepared s))).re) atTop (𝓝 z) := by
  simpa only [← signed_is_matrix_element] using no_finite_cut_net_limit z

theorem strong_projection_error (r : Route) (x : One) :
    Tendsto (fun k => ‖proj (stages r k) x - x‖) atTop (𝓝 0) := by
  simpa using ((stages_strong r x).sub (tendsto_const_nhds (x := x))).norm

theorem third_derivative_of_cutoff (N : ℕ) : iteratedDeriv 3 (NullCone.Series.cutoff N) 0 =
    -6 * Complex.I * (harmonic N : ℂ) := by
  have h := NullCone.Series.cutoff_cubic N
  linear_combination 6 * h

open NullCone.Series NullCone.Perturbation

private def weakCoupling (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹

theorem sampled_cubic_remainder_im :
    Tendsto (fun n : ℕ =>
      ((amplitude (weakCoupling n) - ((Real.pi ^ 2 / 12 * weakCoupling n ^ 2 : ℝ) : ℂ)) /
        ((weakCoupling n ^ 3 : ℝ) : ℂ)).im) atTop atBot := by
  have h : Tendsto weakCoupling atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_inv_atTop_nhdsGT_zero.comp (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  simpa only [Function.comp_def, Complex.div_ofReal_im, Complex.sub_im, Complex.ofReal_im, sub_zero]
    using amplitude_im_cubic_atBot.comp h

private def outsideProjection {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (V : Submodule ℂ E) : E →L[ℂ] E :=
  letI : Vᗮ.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace (K := Vᗮ)
  Vᗮ.starProjection
private theorem outside_diag {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (V : Submodule ℂ E) (x : E) :
    (⟪x, outsideProjection V x⟫_ℂ).re = NullCone.Dilution.outsideMass V x := by
  letI : Vᗮ.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace (K := Vᗮ)
  change RCLike.re (⟪x, Vᗮ.starProjection x⟫_ℂ) = ‖Vᗮ.orthogonalProjection x‖ ^ 2
  rw [inner_re_symm]
  exact Vᗮ.re_inner_starProjection_eq_normSq x

theorem outside_projection_trace_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (A V : Submodule ℂ E) [FiniteDimensional ℂ A]
    (hV : ¬ FiniteDimensional ℂ V) (n : ℕ) :
    ∃ e : Fin (Module.finrank ℂ A + n) → E, Orthonormal ℂ e ∧
      A ≤ Submodule.span ℂ (Set.range e) ∧
      NullCone.Trace.cutWeight (outsideProjection V) e ≤ Module.finrank ℂ A := by
  obtain ⟨e, he, hA, _, hmass⟩ := NullCone.Dilution.exists_diluted_cut A V hV n
  refine ⟨e, he, hA, ?_⟩
  calc
    _ = ∑ i, NullCone.Dilution.outsideMass V (e i) := by
      unfold NullCone.Trace.cutWeight
      apply Finset.sum_congr rfl
      intro i _
      exact outside_diag V (e i)
    _ ≤ _ := hmass

#print axioms five_matrix_element_limits
#print axioms no_finite_matrix_element_net_limit
#print axioms strong_projection_error
#print axioms third_derivative_of_cutoff
#print axioms sampled_cubic_remainder_im
#print axioms outside_projection_trace_bound

end SemanticProbe
