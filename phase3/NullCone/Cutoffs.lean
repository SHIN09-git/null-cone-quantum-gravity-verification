import NullCone.Model

noncomputable section
open Filter Topology
namespace NullCone.Model

inductive Route
  | balanced | positive | zero | negative | dilute
  deriving DecidableEq, Repr

/-- The paper audit counts from n=1. The natural stage k represents n=k+1. -/
def leftCount : Route → ℕ → ℕ
  | .balanced, k => k + 1
  | .positive, k => 3*k + 1
  | .zero, k => 3*k + 3
  | .negative, k => 3*k + 5
  | .dilute, k => 7*(k+1)

def stages (p : Route) (k : ℕ) : Finset Label := labels (leftCount p k) (k+1)

theorem right_le_left (p : Route) (k : ℕ) : k+1 ≤ leftCount p k := by
  cases p <;> simp [leftCount] <;> omega

theorem stages_mono (p : Route) : Monotone (stages p) := by
  intro k l h; apply Finset.disjSum_mono <;> apply Finset.range_mono
  · cases p <;> simp [leftCount] <;> omega
  · omega

theorem stages_cofinal (p : Route) : Tendsto (stages p) atTop atTop := by
  apply (stages_mono p).tendsto_atTop_finset
  rintro (i|i)
  · exact ⟨i, Finset.inl_mem_disjSum.mpr (Finset.mem_range.mpr <| (Nat.lt_succ_self i).trans_le (right_le_left p i))⟩
  · exact ⟨i, Finset.inr_mem_disjSum.mpr (Finset.mem_range.mpr (Nat.lt_succ_self i))⟩

theorem stages_strong (p : Route) (x : One) :
    Tendsto (fun k => proj (stages p k) x) atTop (𝓝 x) :=
  proj_strong_of_cofinal (stages_cofinal p) x

theorem stages_nested (p : Route) {k l : ℕ} (h : k ≤ l) (x : One) :
    proj (stages p l) (proj (stages p k) x) = proj (stages p k) x := by
  apply lp.ext; funext i
  by_cases hi : i ∈ stages p k
  · simp [hi, stages_mono p h hi]
  · simp [hi]

end NullCone.Model

