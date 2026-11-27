import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Sum
import Mathlib.Tactic.Ring

/-! Finite contractions and equal-rank exhaustions of the two-area model in
Section 2 of the Phase 2 re-examination. The labels within a band form two
countable lists, identified with the even and odd labels. -/

namespace NullCone.EqualRank

open Finset
open scoped BigOperators ComplexConjugate

noncomputable section

/-- The real matrix element of the negative swap on one diagonal tensor block. -/
def flipForm (x y : ℂ) : ℝ := -(conj x * y + conj y * x).re

private def bit (p : Prop) [Decidable p] : ℝ := if p then 1 else 0

/-- Twice the change of the swap matrix element, with the centered norm term.
The right boost multiplies the second coefficient by its relative phase. -/
def block (z : ℂ) (a b : Prop) [Decidable a] [Decidable b] : ℝ :=
  let x : ℂ := bit a
  let y : ℂ := bit b
  2 * (flipForm x (z * y) - flipForm x y) -
    (1 - z.re) * (conj x * x + conj y * y).re

private theorem block_eq (z : ℂ) (a b : Prop) [Decidable a] [Decidable b] :
    block z a b = (1 - z.re) * (4 * bit (a ∧ b) - bit a - bit b) := by
  by_cases ha : a <;> by_cases hb : b <;>
    simp [block, flipForm, bit, ha, hb, Complex.add_re]
  all_goals ring

variable {ι : Type*} [DecidableEq ι]

/-- Twice the unnormalized signed amplitude; w is the common Gaussian weight. -/
def twiceAmplitude (w : ℝ) (z : ℂ) (a b : Finset ι) : ℝ :=
  w * ∑ j ∈ a ∪ b, block z (j ∈ a) (j ∈ b)

private theorem sum_bit {s t : Finset ι} (h : t ⊆ s) :
    (∑ j ∈ s, bit (j ∈ t)) = (t.card : ℝ) := by
  simp [bit, Finset.inter_eq_right.mpr h]

/-- The intersection counts the labels on which both members of a swap survive. -/
theorem twiceAmplitude_eq (w : ℝ) (z : ℂ) (a b : Finset ι) :
    twiceAmplitude w z a b =
      w * (1 - z.re) * (4 * ((a ∩ b).card : ℝ) - a.card - b.card) := by
  have hab : a ∩ b ⊆ a ∪ b := Finset.Subset.trans inter_subset_left subset_union_left
  calc
    _ = w * ∑ j ∈ a ∪ b, (1 - z.re) *
        (4 * bit (j ∈ a ∩ b) - bit (j ∈ a) - bit (j ∈ b)) := by
          simp only [twiceAmplitude, block_eq, mem_inter]
    _ = _ := by
      simp only [← mul_sum, sum_sub_distrib, sum_bit hab, sum_bit subset_union_left,
        sum_bit subset_union_right]
      ring

inductive Route
  | aligned | positive | zero | negative | opposed

/-- The two coordinates count the first labels of each parity. -/
def striped (e o : ℕ) : Finset (ℕ ⊕ ℕ) := (range e).disjSum (range o)

private theorem striped_inter (e o f p : ℕ) :
    striped e o ∩ striped f p = striped (min e f) (min o p) := by
  ext i
  cases i <;> simp [striped]

/-- At natural stage k, the table in the note uses n = k + 1. -/
def firstBand (k : ℕ) := striped (5 * (k + 1)) (k + 1)

def evenCount (r : Route) (k : ℕ) : ℕ :=
  match r with
  | .aligned => 5 * (k + 1)
  | .positive => 2 * (k + 1) + 1
  | .zero => 2 * (k + 1)
  | .negative => 2 * k + 1
  | .opposed => k + 1

def secondBand (r : Route) (k : ℕ) :=
  striped (evenCount r k) (6 * (k + 1) - evenCount r k)

theorem same_rank (r : Route) (k : ℕ) :
    (firstBand k).card = 6 * (k + 1) ∧ (secondBand r k).card = 6 * (k + 1) := by
  cases r <;> simp only [firstBand, secondBand, evenCount, striped, card_disjSum, card_range] <;> omega

/-- In each band cuts grow by inclusion and eventually contain each index. -/
theorem exhaustions (r : Route) :
    Monotone firstBand ∧ Monotone (secondBand r) ∧
    ∀ i, ∃ k, i ∈ firstBand k ∧ i ∈ secondBand r k := by
  refine ⟨?_, ?_, ?_⟩
  · intro k l h
    apply disjSum_mono <;> apply range_mono <;> omega
  · intro k l h
    apply disjSum_mono <;> apply range_mono <;> cases r <;> simp only [evenCount] <;> omega
  · rintro (i | i) <;> refine ⟨i, ?_⟩ <;> cases r <;>
      simp only [firstBand, secondBand, evenCount, striped, inl_mem_disjSum, inr_mem_disjSum,
        mem_range] <;> omega

/-- The signed amplitude in units of w(1 − Re z). -/
def value (r : Route) (k : ℕ) : ℤ :=
  match r with
  | .aligned => 6 * (k + 1 : ℤ)
  | .positive => 2
  | .zero => 0
  | .negative => -2
  | .opposed => -2 * (k + 1 : ℤ)

theorem five_values (w : ℝ) (z : ℂ) (r : Route) (k : ℕ) :
    twiceAmplitude w z (firstBand k) (secondBand r k) =
      2 * w * (1 - z.re) * (value r k : ℝ) := by
  have hr := same_rank r k
  have hc : 4 * (((firstBand k ∩ secondBand r k).card : ℕ) : ℤ) -
      (firstBand k).card - (secondBand r k).card = 2 * value r k := by
    rw [hr.1, hr.2]
    simp only [firstBand, secondBand, striped_inter]
    cases r <;> simp only [evenCount, striped, card_disjSum, card_range, value] <;> omega
  have hreal : 4 * ((firstBand k ∩ secondBand r k).card : ℝ) -
      (firstBand k).card - (secondBand r k).card = 2 * (value r k : ℝ) := by
    exact_mod_cast hc
  rw [twiceAmplitude_eq, hreal]
  ring

#print axioms twiceAmplitude_eq
#print axioms same_rank
#print axioms exhaustions
#print axioms five_values

end
end NullCone.EqualRank
