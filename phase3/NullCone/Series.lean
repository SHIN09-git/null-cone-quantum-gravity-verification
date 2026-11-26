import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic

/-!
# The scalar mode series in equations (4.33) and (4.34)

The physical mode number is `k = n + 1`. The coupling variable `x = 1/s` is
real throughout, including in the derivatives. The scalar series is the
starting point of this file.
-/

noncomputable section

open Filter Finset Complex
open scoped Topology

namespace NullCone.Series

/-- The constant multiplying the real argument in the exponential of mode `n + 1`. -/
def frequency (n : ℕ) : ℂ := -2 * I * (n + 1)

/-- One term before multiplication by the common factor `x²/2`. -/
def mode (x : ℝ) (n : ℕ) : ℂ := exp (frequency n * x) / ((n : ℂ) + 1) ^ 2

/-- The hard cutoff keeps precisely the physical modes 1 through `N`. -/
def cutoff (N : ℕ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ 2 / 2 * ∑ n ∈ range N, mode x n

def amplitude (x : ℝ) : ℂ := (x : ℂ) ^ 2 / 2 * ∑' n, mode x n

/-- The defining power series for the dilogarithm, used on the closed unit disk. -/
def dilogSeries (z : ℂ) : ℂ := ∑' n : ℕ, z ^ (n + 1) / ((n : ℂ) + 1) ^ 2

private theorem modeNumber_norm (n : ℕ) : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
  rw [← Nat.cast_one (R := ℂ), ← Nat.cast_add, Complex.norm_natCast]
  push_cast
  rfl

private theorem prefactor_norm (x : ℝ) : ‖(x : ℂ) ^ 2 / 2‖ = x ^ 2 / 2 := by
  simp [norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem mode_norm (x : ℝ) (n : ℕ) :
    ‖mode x n‖ = 1 / ((n : ℝ) + 1) ^ 2 := by
  have hphase : (frequency n * x).re = 0 := by simp [frequency, Complex.mul_re, Complex.mul_im]
  simp [mode, norm_pow, Complex.norm_exp, hphase, modeNumber_norm]

private theorem inverseSquares_hasSum :
    HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
  simpa using (hasSum_nat_add_iff' (f := fun n : ℕ => (1 : ℝ) / n ^ 2) 1).2 hasSum_zeta_two

/-- The sum of the norms includes the full prefactor, for every real coupling. -/
theorem amplitude_absolute_sum (x : ℝ) :
    HasSum (fun n => ‖(x : ℂ) ^ 2 / 2 * mode x n‖) (Real.pi ^ 2 * x ^ 2 / 12) := by
  convert inverseSquares_hasSum.mul_left (x ^ 2 / 2) using 1
  · funext n
    rw [norm_mul, prefactor_norm, mode_norm]
  · ring

/-- The actual finite amplitudes converge as the cutoff is removed. -/
theorem cutoff_tendsto (x : ℝ) :
    Tendsto (fun N => cutoff N x) atTop (𝓝 (amplitude x)) := by
  have hs : Summable (mode x) := .of_norm (by simpa [mode_norm] using inverseSquares_hasSum.summable)
  exact tendsto_const_nhds.mul hs.hasSum.tendsto_sum_nat

/-- The defining power series converges absolutely on the entire closed unit disk. -/
theorem dilogSeries_absolute (z : ℂ) (hz : ‖z‖ ≤ 1) :
    Summable (fun n : ℕ => ‖z ^ (n + 1) / ((n : ℂ) + 1) ^ 2‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ inverseSquares_hasSum.summable
  intro n
  rw [norm_div, norm_pow, norm_pow, modeNumber_norm]
  exact div_le_div_of_nonneg_right (pow_le_one₀ (norm_nonneg z) hz) (sq_nonneg _)

/-- Identify the phase series with the dilogarithm at its unit-circle argument. -/
theorem amplitude_eq_dilog (x : ℝ) :
    amplitude x = (x : ℂ) ^ 2 / 2 * dilogSeries (exp (-2 * I * x)) := by
  unfold amplitude dilogSeries
  congr 1
  apply tsum_congr
  intro n
  rw [mode, ← Complex.exp_nat_mul]
  congr 2
  push_cast
  unfold frequency
  ring

private theorem inverseSquare_step {t : ℝ} (ht : 0 < t) :
    1 / (t + 1) ^ 2 ≤ 1 / t - 1 / (t + 1) := by
  have ht1 : 0 < t + 1 := by linarith
  field_simp
  nlinarith

private theorem inverseSquares_tail_le (N : ℕ) (hN : 0 < N) :
    ∑' n : ℕ, 1 / (((n + N : ℕ) : ℝ) + 1) ^ 2 ≤ 1 / (N : ℝ) := by
  have hsum (M : ℕ) :
      ∑ n ∈ range M, 1 / (((n + N : ℕ) : ℝ) + 1) ^ 2 ≤
        1 / (N : ℝ) - 1 / ((M : ℝ) + N) := by
    induction M with
    | zero => simp
    | succ M ih =>
      rw [sum_range_succ]
      push_cast
      have hm : 0 < (M : ℝ) + N := by positivity
      have hstep := inverseSquare_step hm
      convert add_le_add ih hstep using 1 <;> push_cast <;> ring
  apply Real.tsum_le_of_sum_range_le (fun _ => by positivity)
  intro M
  exact (hsum M).trans (sub_le_self _ (by positivity))

/-- Explicit cutoff error, including the case when the phase is resonant. -/
theorem amplitude_tail_le (x : ℝ) (N : ℕ) (hN : 0 < N) :
    ‖amplitude x - cutoff N x‖ ≤ x ^ 2 / (2 * (N : ℝ)) := by
  have hs : Summable (fun n => ‖mode x n‖) := by simpa [mode_norm] using inverseSquares_hasSum.summable
  have hshift := (summable_nat_add_iff (f := fun n => ‖mode x n‖) N).2 hs
  have htail : ‖∑' n : ℕ, mode x (n + N)‖ ≤ 1 / (N : ℝ) := by
    apply (norm_tsum_le_tsum_norm hshift).trans
    simpa [mode_norm] using inverseSquares_tail_le N hN
  rw [amplitude, cutoff, ← mul_sub, ← hs.of_norm.sum_add_tsum_nat_add N, add_sub_cancel_left,
    norm_mul, prefactor_norm]
  calc
    _ ≤ (x ^ 2 / 2) * (1 / (N : ℝ)) := mul_le_mul_of_nonneg_left htail (by positivity)
    _ = _ := by ring

/-! Finite sums can be differentiated before taking the cutoff limit. -/

private def moment (N j : ℕ) (x : ℝ) : ℂ :=
  ∑ n ∈ range N, frequency n ^ j * mode x n

private theorem moment_deriv (N j : ℕ) (x : ℝ) :
    HasDerivAt (moment N j) (moment N (j + 1) x) x := by
  unfold moment
  apply HasDerivAt.fun_sum
  intro n _
  have hc : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
    simpa using (hasDerivAt_id x).ofReal_comp
  have he := (hc.const_mul (frequency n)).cexp
  convert ((he.div_const (((n : ℂ) + 1) ^ 2)).const_mul (frequency n ^ j)) using 1
  simp [mode, pow_succ]
  ring

private theorem prefactor_deriv (x : ℝ) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ 2 / 2) (x : ℂ) x := by
  have hc : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
    simpa using (hasDerivAt_id x).ofReal_comp
  convert (hc.pow 2).div_const 2 using 1
  ring

private theorem cutoff_deriv (N : ℕ) :
    deriv (cutoff N) = fun x : ℝ =>
      (x : ℂ) * moment N 0 x + (x : ℂ) ^ 2 / 2 * moment N 1 x := by
  funext x
  have hcut : cutoff N = (fun y : ℝ => (y : ℂ) ^ 2 / 2) * moment N 0 := by
    funext y
    simp [cutoff, moment]
  rw [hcut]
  exact ((prefactor_deriv x).mul (moment_deriv N 0 x)).deriv

private theorem cutoff_second (N : ℕ) :
    iteratedDeriv 2 (cutoff N) = fun x : ℝ =>
      moment N 0 x + 2 * (x : ℂ) * moment N 1 x + (x : ℂ) ^ 2 / 2 * moment N 2 x := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, cutoff_deriv]
  funext x
  have hc : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
    simpa using (hasDerivAt_id x).ofReal_comp
  convert ((hc.mul (moment_deriv N 0 x)).add
    ((prefactor_deriv x).mul (moment_deriv N 1 x))).deriv using 1
  ring

private theorem cutoff_third_zero (N : ℕ) :
    iteratedDeriv 3 (cutoff N) 0 = 3 * moment N 1 0 := by
  rw [iteratedDeriv_succ, cutoff_second]
  have hc : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp
  convert (((moment_deriv N 0 0).add ((hc.const_mul 2).mul (moment_deriv N 1 0))).add
    ((prefactor_deriv 0).mul (moment_deriv N 2 0))).deriv using 1
  push_cast
  ring

private theorem firstMoment_zero (N : ℕ) :
    moment N 1 0 = (-2 * I) * (harmonic N : ℂ) := by
  simp only [moment, mode, ofReal_zero, mul_zero, exp_zero, pow_one, harmonic, Rat.cast_sum,
    Rat.cast_inv, Nat.cast_add, Nat.cast_one, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  have hk : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  unfold frequency
  field_simp
  push_cast
  rfl

/-- The cubic Taylor coefficient is the third real derivative divided by `3!`. -/
theorem cutoff_cubic (N : ℕ) :
    iteratedDeriv 3 (cutoff N) 0 / 6 = -I * (harmonic N : ℂ) := by
  rw [cutoff_third_zero, firstMoment_zero]
  ring

/-- The paper's cubic term in Newton's constant, with the fixed proportionality `x = c G`. -/
theorem cutoff_cubic_scaled (N : ℕ) (c G : ℝ) :
    (G : ℂ) ^ 3 / 6 * iteratedDeriv 3 (fun g : ℝ => cutoff N (c * g)) 0 =
      -I * ((c * G : ℝ) : ℂ) ^ 3 * (harmonic N : ℂ) := by
  have hs : ContDiff ℝ 3 (cutoff N) := by
    have hc : ContDiff ℝ 3 (fun y : ℝ => (y : ℂ)) := Complex.ofRealCLM.contDiff
    unfold cutoff mode
    fun_prop (disch := assumption)
  rw [iteratedDeriv_comp_const_smul hs c]
  simp only [mul_zero, Complex.real_smul]
  push_cast
  calc
    _ = (G : ℂ) ^ 3 * (c : ℂ) ^ 3 * (iteratedDeriv 3 (cutoff N) 0 / 6) := by ring
    _ = _ := by rw [cutoff_cubic]; ring

/-- After removing the logarithmic divergence, the limiting constant is Euler's gamma. -/
theorem cubic_log_limit :
    Tendsto (fun N => -(iteratedDeriv 3 (cutoff N) 0 / 6).im - Real.log N) atTop
      (𝓝 Real.eulerMascheroniConstant) := by
  simpa [cutoff_cubic, Complex.mul_im] using Real.tendsto_harmonic_sub_log

theorem cubic_diverges :
    Tendsto (fun N => -(iteratedDeriv 3 (cutoff N) 0 / 6).im) atTop atTop := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  simpa using cubic_log_limit.add_atTop hlog

theorem cubic_no_finite_limit (z : ℂ) :
    ¬ Tendsto (fun N => iteratedDeriv 3 (cutoff N) 0 / 6) atTop (𝓝 z) := by
  intro hz
  exact not_tendsto_nhds_of_tendsto_atTop cubic_diverges (-z.im)
    ((Complex.continuous_im.tendsto z).comp hz).neg

#print axioms mode_norm
#print axioms amplitude_absolute_sum
#print axioms cutoff_tendsto
#print axioms dilogSeries_absolute
#print axioms amplitude_eq_dilog
#print axioms amplitude_tail_le
#print axioms cutoff_cubic
#print axioms cutoff_cubic_scaled
#print axioms cubic_log_limit
#print axioms cubic_diverges
#print axioms cubic_no_finite_limit

end NullCone.Series
