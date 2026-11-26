import NullCone.Projections

noncomputable section
open scoped Polynomial
namespace NullCone.Model
open Polynomial

/-- The area satisfies its two-level polynomial identity on the whole Hilbert space. -/
theorem area_polynomial : (area - 1) * (area - 3) = 0 := by
  ext x i
  change (area ((area - 3) x) i - ((area - 3) x) i) = 0
  rw [area_apply]
  rw [show (3 : One →L[ℂ] One) = 1+1+1 by norm_num]
  change (areaValue i : ℂ) * (area x i - (x i + x i + x i)) - (area x i - (x i + x i + x i)) = 0
  rw [area_apply]; cases i <;> simp [areaValue]
  ring

theorem area_spectrum_subset {s : ℝ} (hs : s ∈ spectrum ℝ area) : s = 1 ∨ s = 3 := by
  let i : Label := .inl 0
  letI : Nontrivial (One →L[ℂ] One) := ⟨⟨1,0, fun h =>
    (ket_orthonormal.ne_zero i) (congrArg (fun A : One →L[ℂ] One => A (ket i)) h)⟩⟩
  let p : ℝ[X] := (X - 1) * (X - 3)
  have hz : aeval area p = 0 := by simpa [p, show aeval area (3 : ℝ[X]) = 3 from aeval_natCast area 3] using area_polynomial
  have hh := spectrum.subset_polynomial_aeval area p ⟨s, hs, rfl⟩
  rw [hz, spectrum.zero_eq] at hh
  simpa [p, sub_eq_zero] using hh

def gaussianWeight (s : ℝ) : ℝ := Real.exp (-s) * Real.exp (-((s-3)^2)/2)
def gaussianCap (s : ℝ) : ℝ := Real.exp (-s/2) * Real.exp (-((s-3)^2)/4)

theorem q_exp : q = Real.exp (-(3:ℝ)/2) := by
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (Real.exp_pos _).le).mp
  change (Real.sqrt w)^2 = _
  rw [Real.sq_sqrt w_pos.le, sq, ← Real.exp_add]; norm_num [w]

/-- Spectral functional calculus of the actual area yields the constant Gaussian weight. -/
theorem weight_is_gaussian : cfc gaussianWeight area = weight := by
  calc
    _ = cfc (fun _ : ℝ => w) area := by
      apply cfc_congr; intro s hs
      rcases area_spectrum_subset hs with rfl|rfl <;> norm_num [gaussianWeight,w, ← Real.exp_add]
    _ = _ := by rw [cfc_const w area area_selfAdjoint]; rfl

theorem cap_is_gaussian : cfc gaussianCap area = cap := by
  calc
    _ = cfc (fun _ : ℝ => q) area := by
      apply cfc_congr; intro s hs
      rw [q_exp]
      rcases area_spectrum_subset hs with rfl|rfl <;> norm_num [gaussianCap, ← Real.exp_add]
    _ = _ := by rw [cfc_const q area area_selfAdjoint]; rfl

theorem area_ket (i : Label) : area (ket i) = (areaValue i : ℂ) • ket i := by
  apply lp.ext; funext j
  rw [area_apply]; by_cases h : j = i
  · subst j; rfl
  · simp [ket, h]

end NullCone.Model

