import NullCone.Model

/-! Finite matrix elements of the same packet, boost and exchange observable at every cutoff. -/

noncomputable section

open Finset Complex
open scoped BigOperators ComplexConjugate InnerProductSpace

namespace NullCone.Model

/-- Squared norm of the prepared two-boundary vector at a rectangular label cutoff. -/
theorem mass_labels (r n : ℕ) : mass (labels r n) = w * ((r : ℝ) + n) := by
  have hinner : inner ℂ (prepared (labels r n)) (prepared (labels r n)) =
      ∑ _i ∈ labels r n, (w : ℂ) := by
    rw [prepared, packet_inner]
    apply sum_congr rfl
    intro i hi
    simp [packet_apply, hi, ← Complex.ofReal_mul, q_sq]
  rw [mass, hinner]
  simp [labels, nsmul_eq_mul, Complex.mul_re]
  ring

private theorem observed_packet (s : Finset Label) (a : Label → ℂ) :
    (inner ℂ (packet s a) (observable (packet s a))).re =
      ∑ i ∈ s, if swap i ∈ s then -(conj (a i) * a (swap i)).re else 0 := by
  rw [packet_inner, Complex.re_sum]
  apply sum_congr rfl
  intro i _
  by_cases h : swap i ∈ s <;> simp [packet_apply, h]

private theorem count_paired (r n : ℕ) (c : ℝ) :
    (∑ j ∈ range r, if j < n then c else 0) = (min r n : ℕ) * c := by
  rw [← Finset.sum_filter]
  have h : (range r).filter (fun j => j < n) = range (min r n) := by
    ext j
    simp
  simp [h, nsmul_eq_mul]

private def bandCoefficients (a b : ℂ) : Label → ℂ := Sum.elim (fun _ => a) (fun _ => b)

private theorem observed_labels {r n : ℕ} (h : n ≤ r) (a b : ℂ) :
    (inner ℂ (packet (labels r n) (bandCoefficients a b))
      (observable (packet (labels r n) (bandCoefficients a b)))).re =
      -(n : ℝ) * ((conj a * b).re + (conj b * a).re) := by
  rw [observed_packet, labels, sum_disjSum]
  simp [swap, bandCoefficients, count_paired, min_eq_left h, min_eq_right h]
  ring

/-- Change in the actual exchange expectation under the right boundary boost. -/
theorem change_labels {r n : ℕ} (h : n ≤ r) :
    change (labels r n) = 2 * w * delta * n := by
  have hu : (fun _ : Label => (q : ℂ)) = bandCoefficients q q := by
    funext i
    cases i <;> rfl
  have hb : (fun i => rightPhase i * (q : ℂ)) = bandCoefficients q (exp I * q) := by
    funext i
    cases i <;> simp [rightPhase, bandCoefficients]
  have hcos : (exp I).re = Real.cos 1 := by simpa using Complex.exp_ofReal_mul_I_re 1
  simp only [change, prepared, boost_packet]
  rw [hb, hu, observed_labels h, observed_labels h]
  simp [Complex.mul_re, Complex.mul_im, hcos, delta]
  have hs : q ^ 2 = w := by simpa [sq] using q_sq
  ring_nf
  rw [hs]
  ring

theorem signed_labels {r n : ℕ} (h : n ≤ r) :
    signed (labels r n) = w * delta * ((3 : ℝ) * n - r) / 2 := by
  rw [signed, change_labels h, mass_labels]
  ring

/-- The boost response of any actual vector of the two-boundary Hilbert space. -/
def response (v : Two) : ℝ :=
  (inner ℂ (rightBoost v) (observable (rightBoost v))).re - (inner ℂ v (observable v)).re

/-- Scale the prepared packet by its Hilbert-space norm. -/
def unitPacket (s : Finset Label) : Two :=
  ((Real.sqrt (mass s))⁻¹ : ℝ) • prepared s

theorem unitPacket_norm (s : Finset Label) (hm : 0 < mass s) : ‖unitPacket s‖ = 1 := by
  have hs : Real.sqrt (mass s) = ‖prepared s‖ := by
    exact (norm_eq_sqrt_re_inner (𝕜 := ℂ) (prepared s)).symm
  rw [unitPacket, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), hs]
  exact inv_mul_cancel₀ (by rw [← hs]; positivity)

private theorem response_real_smul (c : ℝ) (v : Two) :
    response (c • v) = c ^ 2 * response v := by
  change response ((c : ℂ) • v) = _
  simp [response, Complex.mul_re, Complex.mul_im]
  ring

theorem unitPacket_response (s : Finset Label) (hm : 0 < mass s) :
    response (unitPacket s) = change s / mass s := by
  rw [unitPacket, response_real_smul, inv_pow, Real.sq_sqrt hm.le, div_eq_inv_mul]
  rfl

theorem normalized_labels {r n : ℕ} (h : n ≤ r) (hsize : 0 < r + n) :
    response (unitPacket (labels r n)) = 2 * n * delta / ((r : ℝ) + n) := by
  have hn : 0 < (r : ℝ) + n := by exact_mod_cast hsize
  have hm : 0 < mass (labels r n) := by rw [mass_labels]; exact mul_pos w_pos hn
  rw [unitPacket_response _ hm, change_labels h, mass_labels]
  field_simp [w_pos.ne', hn.ne']

/-- The single complete pair, normalized in the same two-boundary space. -/
def referencePair : Two := unitPacket (labels 1 1)

theorem reference_pair_norm : ‖referencePair‖ = 1 := by
  apply unitPacket_norm
  rw [mass_labels]
  exact mul_pos w_pos (by norm_num)

theorem reference_pair_response : response referencePair = delta := by
  calc
    _ = 2 * (1 : ℝ) * delta / (1 + 1) := by
      simpa only [referencePair, Nat.cast_one] using
        normalized_labels (r := 1) (n := 1) (by decide) (by decide)
    _ = _ := by ring

#print axioms mass_labels
#print axioms change_labels
#print axioms signed_labels
#print axioms unitPacket_norm
#print axioms unitPacket_response
#print axioms normalized_labels
#print axioms reference_pair_norm
#print axioms reference_pair_response

end NullCone.Model
