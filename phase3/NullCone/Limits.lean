import NullCone.Cutoffs
import NullCone.Amplitude
import NullCone.Projections

noncomputable section
open Filter Topology
namespace NullCone.Model

theorem rank_stages (p : Route) (k : ℕ) :
    Module.finrank ℂ (LinearMap.range (proj (stages p k)).toLinearMap) = leftCount p k + (k+1) := by
  rw [(proj_finite_rank _).2]; simp [stages,labels]

private theorem step (p : Route) (k : ℕ) : signed (stages p k) =
    w * delta * (3 * ((k : ℝ)+1) - leftCount p k) / 2 := by
  simpa only [stages, Nat.cast_add, Nat.cast_one] using signed_labels (right_le_left p k)

theorem signed_by_route (p : Route) (k : ℕ) :
    signed (stages p k) = match p with
    | .balanced => w*delta*((k:ℝ)+1)
    | .positive => w*delta
    | .zero => 0
    | .negative => -(w*delta)
    | .dilute => -(2*w*delta)*((k:ℝ)+1) := by
  rw [step]; cases p <;> simp only [leftCount, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] <;> ring

private theorem index_grows : Tendsto (fun k : ℕ => (k:ℝ)+1) atTop atTop :=
  tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop

theorem balanced_limit : Tendsto (fun k => signed (stages .balanced k)) atTop atTop := by
  simp only [signed_by_route]
  exact index_grows.const_mul_atTop (mul_pos w_pos delta_pos)

theorem positive_limit : Tendsto (fun k => signed (stages .positive k)) atTop (𝓝 (w*delta)) := by
  simp only [signed_by_route]; exact tendsto_const_nhds

theorem zero_limit : Tendsto (fun k => signed (stages .zero k)) atTop (𝓝 0) := by
  simp only [signed_by_route]; exact tendsto_const_nhds

theorem negative_limit : Tendsto (fun k => signed (stages .negative k)) atTop (𝓝 (-(w*delta))) := by
  simp only [signed_by_route]; exact tendsto_const_nhds

theorem dilute_limit : Tendsto (fun k => signed (stages .dilute k)) atTop atBot := by
  simp only [signed_by_route]
  exact index_grows.const_mul_atTop_of_neg (by have := mul_pos w_pos delta_pos; linarith)

theorem reference_match (k : ℕ) :
    signed (stages .positive k) = signed (labels 1 1) ∧ 0 < signed (stages .positive k) := by
  have href : labels 1 1 = stages .balanced 0 := rfl
  rw [href,signed_by_route,signed_by_route]; simp [w_pos,delta_pos]

/-- The directed net over *all* finite coordinate sets has no common finite value. -/
theorem no_finite_cut_net_limit (z : ℝ) :
    ¬ Tendsto (signed : Finset Label → ℝ) atTop (𝓝 z) := by
  intro h
  have hz : 0 = z := tendsto_nhds_unique zero_limit (h.comp (stages_cofinal .zero))
  have hp : w*delta = z := tendsto_nhds_unique positive_limit (h.comp (stages_cofinal .positive))
  linarith [mul_pos w_pos delta_pos]

end NullCone.Model

