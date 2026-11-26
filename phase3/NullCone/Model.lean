import NullCone.Hilbert

noncomputable section
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology
namespace NullCone.Model

abbrev Label := ℕ ⊕ ℕ
abbrev One := H Label
abbrev Two := H (Label × Label)

def areaValue : Label → ℝ := Sum.elim (fun _ => 1) (fun _ => 3)

def area : One →L[ℂ] One := ContinuousLinearMap.id ℂ One +
  (2 : ℂ) • diag (fun i : Label => if i.isRight then 1 else 0) (fun i => by by_cases h : i.isRight <;> simp [h])

@[simp] theorem area_apply (x : One) (i : Label) : area x i = (areaValue i : ℂ) * x i := by
  cases i <;> simp [areaValue, area, lp.coeFn_smul]
  ring

theorem area_symmetric (x y : One) : inner ℂ (area x) y = inner ℂ x (area y) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]; apply tsum_congr; intro i
  simp [RCLike.inner_apply, mul_left_comm, mul_assoc]

def swap : Equiv.Perm Label := Equiv.sumComm ℕ ℕ
def flip : One ≃ₗᵢ[ℂ] One := perm swap
def both : Equiv.Perm (Label × Label) := Equiv.prodCongr swap swap
def observable : Two →L[ℂ] Two := -(perm both).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem swap_swap (i : Label) : swap (swap i) = i := by cases i <;> rfl
@[simp] theorem flip_apply (x : One) (i : Label) : flip x i = x (swap i) := rfl
@[simp] theorem observable_apply (v : Two) (i j : Label) :
    observable v (i,j) = -v (swap i,swap j) := rfl

theorem flip_involution (x : One) : flip (flip x) = x := by
  apply lp.ext; funext i; simp
theorem observable_involution (v : Two) : observable (observable v) = v := by
  apply lp.ext; funext ⟨i,j⟩; simp
theorem observable_symmetric (x y : Two) : inner ℂ (observable x) y = inner ℂ x (observable y) := by
  have hh (v : Two) : perm both (perm both v) = v := by
    apply lp.ext; funext ⟨i,j⟩; change v (swap (swap i),swap (swap j)) = _; simp
  have ht := (perm both).inner_map_map x (perm both y)
  rw [hh] at ht
  simpa [observable] using congrArg Neg.neg ht

def w : ℝ := Real.exp (-3)
def q : ℝ := Real.sqrt w
def cap : One →L[ℂ] One := (q : ℂ) • ContinuousLinearMap.id ℂ One
def weight : One →L[ℂ] One := (w : ℂ) • ContinuousLinearMap.id ℂ One
theorem w_pos : 0 < w := Real.exp_pos _
theorem q_sq : q * q = w := Real.mul_self_sqrt w_pos.le

theorem gaussian (i : Label) :
    Real.exp (-areaValue i) * Real.exp (-((areaValue i - 3)^2) / 2) = w := by
  rw [← Real.exp_add]; cases i <;> norm_num [areaValue,w]

theorem cap_weight (x y : One) : inner ℂ (cap x) (cap y) = inner ℂ x (weight y) := by
  simp [cap, weight, ← mul_assoc, ← Complex.ofReal_mul, q_sq]

def rightPhase : Label → ℂ := Sum.elim (fun _ => 1) (fun _ => Complex.exp Complex.I)
theorem rightPhase_unit (i : Label) : ‖rightPhase i‖ = 1 := by
  cases i <;> simp [rightPhase, Complex.norm_exp]

theorem boost_phase_from_area (i : Label) :
    Complex.exp (Complex.I * (areaValue i : ℂ) / 2) =
      Complex.exp (Complex.I / 2) * rightPhase i := by
  cases i with
  | inl j => simp [areaValue, rightPhase]
  | inr j =>
    simp only [areaValue,rightPhase,Sum.elim_inr, Complex.ofReal_ofNat, ← Complex.exp_add]
    congr 1
    ring

def rightBoost : Two →L[ℂ] Two :=
  diag (fun p : Label × Label => rightPhase p.2) (fun p => (rightPhase_unit p.2).le)

theorem boost_isometry (v : Two) : ‖rightBoost v‖ = ‖v‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ENNReal).toReal),
      lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ENNReal).toReal)]
  simp [rightBoost, rightPhase_unit]

theorem proj_area_commute (s : Finset Label) (x : One) :
    proj s (area x) = area (proj s x) := by
  apply lp.ext; funext i; by_cases h : i ∈ s <;> simp [h]
theorem proj_weight_commute (s : Finset Label) (x : One) :
    proj s (weight x) = weight (proj s x) := by simp [weight]

def labels (r n : ℕ) : Finset Label := (Finset.range r).disjSum (Finset.range n)

/-- Finite diagonal packet on the full two-label complex Hilbert space. -/
def packet (s : Finset Label) (a : Label → ℂ) : Two :=
  ∑ i ∈ s, lp.single 2 (i,i) (a i)

theorem packet_apply (s : Finset Label) (a : Label → ℂ) (i j : Label) :
    packet s a (i,j) = if i = j ∧ i ∈ s then a i else 0 := by
  simp only [packet, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single, Pi.single_apply]
  by_cases hij : i = j
  · subst j
    simp [Prod.ext_iff]
  · have hne (k : Label) : (i,j) ≠ (k,k) := fun h => hij ((congrArg Prod.fst h).trans (congrArg Prod.snd h).symm)
    simp [hne,hij]

theorem packet_inner (s : Finset Label) (a : Label → ℂ) (v : Two) :
    inner ℂ (packet s a) v = ∑ i ∈ s, conj (a i) * v (i,i) := by
  simp [packet, lp.inner_single_left, RCLike.inner_apply, mul_comm]

def prepared (s : Finset Label) : Two := packet s (fun _ => (q : ℂ))

theorem prepared_matrix (s : Finset Label) (i j : Label) :
    prepared s (i,j) = inner ℂ (ket i) (cap (proj s (ket j))) := by
  rw [ket_inner]; simp only [prepared, packet_apply, cap, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, proj_apply,
    ket, lp.coeFn_single, Pi.single_apply]
  by_cases hij : i = j <;> by_cases hi : i ∈ s <;> simp [hij, hi]

theorem boost_packet (s : Finset Label) (a : Label → ℂ) :
    rightBoost (packet s a) = packet s (fun i => rightPhase i * a i) := by
  apply lp.ext; funext ⟨i,j⟩
  simp only [rightBoost, diag_apply, packet_apply]
  by_cases h : i = j ∧ i ∈ s
  · simp [h]
  · simp [h]

def delta : ℝ := 1 - Real.cos 1
theorem delta_pos : 0 < delta := by
  have h := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl (0:ℝ)) (by linarith [Real.pi_gt_three] : 1 ≤ Real.pi) (by norm_num : (0:ℝ)<1)
  simpa [delta, sub_pos] using h

def mass (s : Finset Label) : ℝ := (inner ℂ (prepared s) (prepared s)).re
def change (s : Finset Label) : ℝ :=
  (inner ℂ (rightBoost (prepared s)) (observable (rightBoost (prepared s)))).re -
  (inner ℂ (prepared s) (observable (prepared s))).re
def signed (s : Finset Label) : ℝ := change s - delta / 2 * mass s

end NullCone.Model

