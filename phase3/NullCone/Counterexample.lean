import NullCone.Limits
import NullCone.Area

noncomputable section
open Filter Topology
namespace NullCone.Model

theorem weight_trace_infinite : NullCone.Trace.positiveTrace weight = ⊤ := by
  by_contra h
  apply model_infinite
  exact NullCone.Trace.finiteDimensional_of_positiveTrace_ne_top weight w_pos (le_refl _) h

theorem positive_route_normalized_limit :
    Tendsto (fun k => response (unitPacket (stages .positive k))) atTop (𝓝 (delta/2)) := by
  have hstep (k : ℕ) :
      response (unitPacket (stages .positive k)) = delta/2 + delta/(4*(k:ℝ)+2) := by
    unfold stages
    rw [normalized_labels (right_le_left .positive k) (by omega)]
    simp only [leftCount, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    field_simp
    ring
  simp_rw [hstep]
  have hg : Tendsto (fun k : ℕ => 4*(k:ℝ)+2) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num))
  simpa using (tendsto_const_nhds (x := delta/2)).add (hg.const_div_atTop delta)

/-- A fixed space, preparation and bounded insertion witness the failed implication. -/
theorem open_gluing_with_incompatible_closures :
    (¬FiniteDimensional ℂ One) ∧
    (∀ x y : One, HasSum (fun i : Label => inner ℂ y (ket i) * inner ℂ (ket i) x) (inner ℂ y x) ∧
      Summable (fun i : Label => ‖inner ℂ y (ket i) * inner ℂ (ket i) x‖)) ∧
    (∀ p x, Tendsto (fun k => proj (stages p k) x) atTop (𝓝 x)) ∧
    (∀ s, signed s = (inner ℂ (prepared s) (insertion (prepared s))).re) ∧
    (∀ k, signed (stages .positive k) = signed (labels 1 1) ∧ 0 < signed (stages .positive k)) ∧
    Tendsto (fun k => signed (stages .dilute k)) atTop atBot :=
  ⟨model_infinite, model_open, stages_strong, signed_is_matrix_element, reference_match, dilute_limit⟩

end NullCone.Model

