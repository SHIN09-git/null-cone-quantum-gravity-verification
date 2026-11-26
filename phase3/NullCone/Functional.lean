import NullCone.Trace

/-!
# A finite positive functional with the prescribed weights on finite projections

The functional is defined on every bounded operator on the same Hilbert space.
Its value at the identity bounds the ordinary positive trace once its values on
finite orthogonal projections agree with the geometric weights.
-/

noncomputable section

open scoped ENNReal InnerProductSpace

namespace NullCone.Functional

open NullCone.Trace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Orthogonal projection onto the finite-dimensional span of the given vectors. -/
def cutProjection {n : ℕ} (e : Fin n → H) : H →L[ℂ] H :=
  let V := Submodule.span ℂ (Set.range e)
  letI : FiniteDimensional ℂ V := FiniteDimensional.span_of_finite ℂ (Set.finite_range e)
  V.starProjection

theorem cutProjection_isStarProjection {n : ℕ} (e : Fin n → H) : IsStarProjection (cutProjection e) := by
  letI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range e)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range e)
  exact isStarProjection_starProjection (U := Submodule.span ℂ (Set.range e))

/-- A positive functional takes every positive bounded operator to a nonnegative real. -/
def IsPositiveFunctional (ζ : (H →L[ℂ] H) →ₗ[ℂ] ℂ) : Prop :=
  ∀ A, A.IsPositive → ∃ t : ℝ, 0 ≤ t ∧ ζ A = (t : ℂ)

/-- On each finite orthonormal family the functional must reproduce the
geometric weight for the orthogonal projection onto that family's span. -/
def AgreesOnFiniteCuts (ζ : (H →L[ℂ] H) →ₗ[ℂ] ℂ) (W : H →L[ℂ] H) : Prop :=
  ∀ (n : ℕ) (e : Fin n → H), Orthonormal ℂ e → (ζ (cutProjection e)).re = cutWeight W e

theorem positiveTrace_le_functional_one (W : H →L[ℂ] H) (ζ : (H →L[ℂ] H) →ₗ[ℂ] ℂ)
    (hpos : IsPositiveFunctional ζ) (hgeom : AgreesOnFiniteCuts ζ W) :
    positiveTrace W ≤ ENNReal.ofReal (ζ 1).re := by
  refine iSup_le fun n => iSup_le fun e => iSup_le fun he => ?_
  rw [← hgeom _ _ he]
  apply ENNReal.ofReal_le_ofReal
  obtain ⟨t, ht, h⟩ := hpos (1 - cutProjection e)
    (ContinuousLinearMap.IsPositive.of_isStarProjection (cutProjection_isStarProjection e).one_sub)
  have hr := congrArg Complex.re h
  rw [map_sub, Complex.sub_re, Complex.ofReal_re] at hr
  linarith

/-- Coercivity and finite positive measurement of every weighted cut imply finite dimension. -/
theorem finiteDimensional_of_weighted_functional (W : H →L[ℂ] H) {c : ℝ} (hc : 0 < c)
    (hW : (c : ℂ) • (1 : H →L[ℂ] H) ≤ W) (ζ : (H →L[ℂ] H) →ₗ[ℂ] ℂ)
    (hpos : IsPositiveFunctional ζ) (hgeom : AgreesOnFiniteCuts ζ W) :
    FiniteDimensional ℂ H :=
  finiteDimensional_of_positiveTrace_ne_top W hc hW
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (positiveTrace_le_functional_one W ζ hpos hgeom))

#print axioms cutProjection_isStarProjection
#print axioms positiveTrace_le_functional_one
#print axioms finiteDimensional_of_weighted_functional

end NullCone.Functional

