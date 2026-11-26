import NullCone.Series
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Weak-coupling limits of the infinite amplitude in (4.33), after cutoff removal. -/

noncomputable section

open Complex Filter Finset
open scoped Topology

namespace NullCone.Perturbation

open NullCone.Series

private theorem inverseSquares :
    HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
  simpa using (hasSum_nat_add_iff' (f := fun n : ℕ => (1 : ℝ) / n ^ 2) 1).2 hasSum_zeta_two

private theorem modeSum_zero :
    (∑' n, mode 0 n) = ((Real.pi ^ 2 / 6 : ℝ) : ℂ) := by
  calc
    _ = ∑' n : ℕ, ((1 / ((n : ℝ) + 1) ^ 2 : ℝ) : ℂ) := by
      apply tsum_congr
      intro n
      simp [mode]
    _ = _ := by rw [← Complex.ofReal_tsum, inverseSquares.tsum_eq]

/-- The summed amplitude has the real quadratic coefficient π²/12, from either side. -/
theorem amplitude_quadratic_limit :
    Tendsto (fun x : ℝ => amplitude x / (x : ℂ) ^ 2) (𝓝[≠] 0)
      (𝓝 ((Real.pi ^ 2 / 12 : ℝ) : ℂ)) := by
  have hc : Continuous (fun x : ℝ => ∑' n, mode x n) := by
    apply continuous_tsum (u := fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) _ inverseSquares.summable
    · intro n x
      exact (mode_norm x n).le
    · intro n
      unfold mode
      fun_prop
  have ht := (hc.tendsto 0).div_const (2 : ℂ)
  have hv : ((Real.pi ^ 2 / 6 : ℝ) : ℂ) / 2 = ((Real.pi ^ 2 / 12 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [modeSum_zero, hv] at ht
  apply (ht.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
  unfold amplitude
  field_simp

private theorem mode_im (x : ℝ) (n : ℕ) :
    (mode x n).im = -Real.sin (2 * ((n : ℝ) + 1) * x) / ((n : ℝ) + 1) ^ 2 := by
  have hphase : frequency n * (x : ℂ) = ((-(2 * ((n : ℝ) + 1) * x) : ℝ) : ℂ) * I := by
    unfold frequency
    push_cast
    ring
  have hden : ((n : ℂ) + 1) ^ 2 = ((((n : ℝ) + 1) ^ 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [mode, hphase, hden, Complex.div_ofReal_im, Complex.exp_ofReal_mul_I_im, Real.sin_neg]

private theorem half_le_sin {y : ℝ} (hy : 0 ≤ y) (hy' : y ≤ 1) : y / 2 ≤ Real.sin y := by
  have hpi : (1 / 2 : ℝ) ≤ 2 / Real.pi :=
    (le_div_iff₀ Real.pi_pos).2 (by linarith [Real.pi_lt_four])
  calc
    _ = (1 / 2) * y := by ring
    _ ≤ 2 / Real.pi * y := mul_le_mul_of_nonneg_right hpi hy
    _ ≤ _ := Real.mul_le_sin hy (by linarith [Real.pi_gt_three])

/-- A cutoff with all phases between zero and one retains half the harmonic divergence. -/
private theorem cutoff_im_bound (N : ℕ) (x : ℝ) (hx : 0 < x) (hphase : 2 * N * x ≤ 1) :
    (cutoff N x).im ≤ -(x ^ 3) * (harmonic N : ℝ) / 2 := by
  have hterm (n : ℕ) (hn : n ∈ range N) : (mode x n).im ≤ -x / ((n : ℝ) + 1) := by
    have hk : (n : ℝ) + 1 ≤ N := by exact_mod_cast Nat.succ_le_of_lt (mem_range.mp hn)
    have hpos : 0 < (n : ℝ) + 1 := by positivity
    have hp : 2 * ((n : ℝ) + 1) * x ≤ 1 := by
      nlinarith only [hphase, mul_le_mul_of_nonneg_right hk hx.le]
    have hs := half_le_sin (by positivity : 0 ≤ 2 * ((n : ℝ) + 1) * x) hp
    rw [mode_im]
    calc
      _ ≤ -(x * ((n : ℝ) + 1)) / ((n : ℝ) + 1) ^ 2 :=
        div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)
      _ = _ := by field_simp
  have hsum : (∑ n ∈ range N, (mode x n).im) ≤ -x * (harmonic N : ℝ) := by
    apply (sum_le_sum hterm).trans_eq
    simp [harmonic, mul_sum, div_eq_mul_inv]
  have hpref : (x : ℂ) ^ 2 / 2 = ((x ^ 2 / 2 : ℝ) : ℂ) := by push_cast; rfl
  calc
    (cutoff N x).im = x ^ 2 / 2 * ∑ n ∈ range N, (mode x n).im := by
      rw [cutoff, hpref, Complex.mul_im, Complex.im_sum]
      simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    _ ≤ x ^ 2 / 2 * (-x * (harmonic N : ℝ)) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

/-- Choose N with 1/4 ≤ Nx ≤ 1/2; the tail contributes at most 2 to the cubic quotient. -/
private theorem amplitude_im_bound (N : ℕ) (x : ℝ) (hx : 0 < x) (hN : 0 < N)
    (hl : 1 ≤ 4 * (N : ℝ) * x) (hu : 2 * (N : ℝ) * x ≤ 1) :
    (amplitude x).im / x ^ 3 ≤ 2 - (harmonic N : ℝ) / 2 := by
  have htail : (amplitude x).im - (cutoff N x).im ≤ x ^ 2 / (2 * (N : ℝ)) :=
    (Complex.im_le_norm (amplitude x - cutoff N x)).trans (amplitude_tail_le x N hN)
  have hsize : x ^ 2 / (2 * (N : ℝ)) ≤ 2 * x ^ 3 := by
    apply (div_le_iff₀ (by positivity)).2
    nlinarith only [mul_le_mul_of_nonneg_left hl (sq_nonneg x)]
  apply (div_le_iff₀ (by positivity)).2
  nlinarith only [htail, hsize, cutoff_im_bound N x hx hu]

/-- The imaginary cubic quotient of the *infinite* amplitude tends to −∞ as x ↓ 0. -/
theorem amplitude_im_cubic_atBot :
    Tendsto (fun x : ℝ => (amplitude x).im / x ^ 3) (𝓝[>] 0) atBot := by
  let N (x : ℝ) := ⌊x⁻¹ / 2⌋₊
  have hN : Tendsto N (𝓝[>] 0) atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_inv_nhdsGT_zero.atTop_div_const (by norm_num : (0:ℝ)<2))
  have hH : Tendsto (fun n : ℕ => (harmonic n : ℝ)) atTop atTop := by
    simpa [cutoff_cubic, Complex.mul_im] using cubic_diverges
  apply tendsto_atBot.2
  intro b
  filter_upwards [(hH.comp hN).eventually_ge_atTop (4 - 2 * b), hN.eventually_ge_atTop 1,
    self_mem_nhdsWithin] with x hhb hn hx
  have hpos : 0 < x := hx
  have hn1 : 1 ≤ (N x : ℝ) := by exact_mod_cast hn
  have hmul : x * (x⁻¹ / 2) = 1 / 2 := by field_simp
  have hl := mul_lt_mul_of_pos_left (Nat.lt_floor_add_one (x⁻¹ / 2)) hpos
  have hu := mul_le_mul_of_nonneg_left (Nat.floor_le (by positivity : 0 ≤ x⁻¹ / 2)) hpos.le
  change x * (x⁻¹ / 2) < x * ((N x : ℝ) + 1) at hl
  change x * (N x : ℝ) ≤ x * (x⁻¹ / 2) at hu
  have hsmall : 1 ≤ 4 * (N x : ℝ) * x := by
    nlinarith only [hl, hmul, mul_le_mul_of_nonneg_left hn1 hpos.le]
  have hlarge : 2 * (N x : ℝ) * x ≤ 1 := by nlinarith only [hu, hmul]
  apply (amplitude_im_bound (N x) x hpos hn hsmall hlarge).trans
  change 4 - 2 * b ≤ (harmonic (N x) : ℝ) at hhb
  linarith

/-- In particular, x_N = 1/(2N) exhibits the divergence with the infinite sum already taken. -/
theorem amplitude_im_cubic_sequence :
    Tendsto (fun N : ℕ => (amplitude (1 / (2 * (N : ℝ)))).im / (1 / (2 * (N : ℝ))) ^ 3)
      atTop atBot := by
  have h : Tendsto (fun N : ℕ => 2 * (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  simpa [Function.comp_def, one_div] using
    amplitude_im_cubic_atBot.comp (tendsto_inv_atTop_nhdsGT_zero.comp h)

/-- The complex cubic quotient after removing the actual quadratic term has no finite right limit. -/
theorem amplitude_no_cubic_coefficient (c : ℂ) :
    ¬ Tendsto (fun x : ℝ =>
      (amplitude x - ((Real.pi ^ 2 / 12 * x ^ 2 : ℝ) : ℂ)) / ((x ^ 3 : ℝ) : ℂ))
        (𝓝[>] 0) (𝓝 c) := by
  intro hc
  have hh := (Complex.continuous_im.tendsto c).comp hc
  apply not_tendsto_nhds_of_tendsto_atBot amplitude_im_cubic_atBot c.im
  simpa only [Function.comp_def, Complex.div_ofReal_im, Complex.sub_im, Complex.ofReal_im,
    sub_zero] using hh

#print axioms amplitude_quadratic_limit
#print axioms amplitude_im_cubic_atBot
#print axioms amplitude_im_cubic_sequence
#print axioms amplitude_no_cubic_coefficient

end NullCone.Perturbation
