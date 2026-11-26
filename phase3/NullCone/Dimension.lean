import NullCone.Trace

/-!
# Finite dimension from the same family of signed cuts

The cut index fixes its orthonormal family, weight, and response. The geometric
hypotheses produce high ranks with small response. The separate closing
hypothesis gives a lower bound or a limit on these same cuts.
-/

noncomputable section

open scoped InnerProductSpace Topology
open Filter NullCone.Trace

namespace NullCone.Dimension

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every infinite-dimensional Hilbert space has orthonormal families of every finite size. -/
theorem exists_orthonormal_fin (hH : ¬ FiniteDimensional ℂ H) (n : ℕ) :
    ∃ v : Fin n → H, Orthonormal ℂ v := by
  classical
  obtain ⟨ι, b, _⟩ := exists_hilbertBasis ℂ H
  rcases finite_or_infinite ι with hι | hι
  · letI := Fintype.ofFinite ι
    exact (hH (FiniteDimensional.of_fintype_basis b.toOrthonormalBasis.toBasis)).elim
  · let j : Fin n → ι := fun i => Infinite.natEmbedding ι i.val
    exact ⟨b ∘ j, b.orthonormal.comp j ((Infinite.natEmbedding ι).injective.comp Fin.val_injective)⟩

variable {ι : Type*} (W : H →L[ℂ] H) (rank : ι → ℕ) (e : (i : ι) → Fin (rank i) → H)
    (he : ∀ i, Orthonormal ℂ (e i)) (response : ι → ℝ)
    {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) (hW : (c : ℂ) • (1 : H →L[ℂ] H) ≤ W)

include he hc hδ hW in
/-- Any finite orthonormal test family can be matched in cardinality by a small-response cut.
A common lower bound on those cuts then forces finite dimension of the ambient space. -/
theorem finiteDimensional_of_cofinal_small_cuts {L : ℝ}
    (hselect : ∀ (n : ℕ) (v : Fin n → H), Orthonormal ℂ v →
      ∃ i, n ≤ rank i ∧ |response i| ≤ δ / 4)
    (hlower : ∀ i, |response i| ≤ δ / 4 →
      L ≤ signedClosure (cutWeight W (e i)) (response i) δ) :
    FiniteDimensional ℂ H := by
  by_contra hH
  let k := c * δ / 4
  have hk : 0 < k := by dsimp [k]; positivity
  obtain ⟨n, hn⟩ := exists_nat_gt (-L / k)
  obtain ⟨v, hv⟩ := exists_orthonormal_fin hH n
  obtain ⟨i, hi, hsmall⟩ := hselect n v hv
  have hni : (n : ℝ) ≤ rank i := by exact_mod_cast hi
  have hlarge := (div_lt_iff₀ hk).mp (hn.trans_le hni)
  have hbound : L ≤ -k * rank i :=
    (hlower i hsmall).trans (signedCut_le_neg_rank W hc hδ hW (he i) hsmall)
  linarith

include he hc hδ hW in
/-- A finite limit bounds the closures on a tail. The small-response cuts with sufficiently
large rank must be present in every tail of this same filter. -/
theorem finiteDimensional_of_cofinal_small_cuts_limit {l : Filter ι} {a : ℝ}
    (hselect : ∀ (n : ℕ) (v : Fin n → H), Orthonormal ℂ v →
      ∃ᶠ i in l, n ≤ rank i ∧ |response i| ≤ δ / 4)
    (hlim : Tendsto (fun i => signedClosure (cutWeight W (e i)) (response i) δ) l (𝓝 a)) :
    FiniteDimensional ℂ H := by
  let S := {i : ι // a - 1 ≤ signedClosure (cutWeight W (e i)) (response i) δ}
  apply finiteDimensional_of_cofinal_small_cuts W (fun i : S => rank i)
    (fun i => e i) (fun i => he i) (fun i => response i) hc hδ hW (L := a - 1)
  · intro n v hv
    have htail := hlim.eventually (lt_mem_nhds (show a - 1 < a by linarith))
    obtain ⟨i, ⟨hni, hsmall⟩, hi⟩ := ((hselect n v hv).and_eventually htail).exists
    exact ⟨⟨i, hi.le⟩, hni, hsmall⟩
  · exact fun i _ => i.property

/-- Choose a positive band width and an integer cycle length *before* increasing the cut rank.
The moment bound then ensures the required response threshold, also when the response
coefficient vanishes. -/
theorem exists_narrow_band_parameters {K A c δ : ℝ} (hK : 0 ≤ K) (hc : 0 < c)
    (hδ : 0 < δ) :
    ∃ (width : ℝ) (m : ℕ), 0 < width ∧ 2 ≤ m ∧
      ∀ q : ℝ, q ≤ width ^ 2 + A ^ 2 / ((m : ℝ) * c) → K * Real.sqrt q ≤ δ / 4 := by
  let width := δ / (8 * (K + 1))
  have hw : 0 < width := by dsimp [width]; positivity
  obtain ⟨m, hm⟩ := exists_nat_gt (max 1 (A ^ 2 / (c * width ^ 2)))
  have hmreal : (1 : ℝ) < m := (le_max_left _ _).trans_lt hm
  have hmnat : 1 < m := by exact_mod_cast hmreal
  refine ⟨width, m, hw, hmnat, ?_⟩
  intro q hq
  have hA := (div_lt_iff₀ (by positivity : 0 < c * width ^ 2)).mp
    ((le_max_right _ _).trans_lt hm)
  have hcycle : A ^ 2 / ((m : ℝ) * c) ≤ width ^ 2 := by
    apply (div_le_iff₀ (mul_pos (by linarith : 0 < (m : ℝ)) hc)).mpr
    nlinarith only [hA]
  have hsqrt : Real.sqrt q ≤ 2 * width := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by positivity, by nlinarith [sq_nonneg width]⟩
  have hid : width * (8 * (K + 1)) = δ :=
    div_mul_cancel₀ _ (ne_of_gt (by positivity : 0 < 8 * (K + 1)))
  exact (mul_le_mul_of_nonneg_left hsqrt hK).trans (by nlinarith)

include he hc hδ hW in
/-- Fix the band and cycle length, then test a single family of cuts. Under the
infinite-dimensional hypothesis the cycles must realize the displayed area-moment
bound at ranks as large as any finite orthonormal test family. -/
theorem finiteDimensional_of_narrow_band_cuts (moment : ι → ℝ) (width A : ℝ) (m : ℕ)
    {K L : ℝ} (hK : 0 ≤ K)
    (hparameters : 0 < width ∧ 2 ≤ m ∧
      K * Real.sqrt (width ^ 2 + A ^ 2 / ((m : ℝ) * c)) ≤ δ / 4)
    (hresponse : ∀ i, |response i| ≤ K * Real.sqrt (moment i))
    (hgeometry : ¬ FiniteDimensional ℂ H →
      ∀ (n : ℕ) (v : Fin n → H), Orthonormal ℂ v →
        ∃ i, n ≤ rank i ∧ moment i ≤ width ^ 2 + A ^ 2 / ((m : ℝ) * c))
    (hlower : ∀ i, |response i| ≤ δ / 4 →
      L ≤ signedClosure (cutWeight W (e i)) (response i) δ) :
    FiniteDimensional ℂ H := by
  by_contra hH
  apply hH
  apply finiteDimensional_of_cofinal_small_cuts W rank e he response hc hδ hW _ hlower
  intro n v hv
  obtain ⟨i, hi, hvariance⟩ := hgeometry hH n v hv
  have hbound := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hvariance) hK
  exact ⟨i, hi, (hresponse i).trans (hbound.trans hparameters.2.2)⟩

include he hc hδ hW in
/-- A finite limit on this fixed family also suffices if the moment-controlled
cuts with arbitrarily large rank appear in every tail. -/
theorem finiteDimensional_of_narrow_band_limit (moment : ι → ℝ) (width A : ℝ) (m : ℕ)
    {K a : ℝ} {l : Filter ι} (hK : 0 ≤ K)
    (hparameters : 0 < width ∧ 2 ≤ m ∧
      K * Real.sqrt (width ^ 2 + A ^ 2 / ((m : ℝ) * c)) ≤ δ / 4)
    (hresponse : ∀ i, |response i| ≤ K * Real.sqrt (moment i))
    (hgeometry : ¬ FiniteDimensional ℂ H →
      ∀ (n : ℕ) (v : Fin n → H), Orthonormal ℂ v →
        ∃ᶠ i in l, n ≤ rank i ∧ moment i ≤ width ^ 2 + A ^ 2 / ((m : ℝ) * c))
    (hlim : Tendsto (fun i => signedClosure (cutWeight W (e i)) (response i) δ) l (𝓝 a)) :
    FiniteDimensional ℂ H := by
  by_contra hH
  apply hH
  apply finiteDimensional_of_cofinal_small_cuts_limit W rank e he response hc hδ hW _ hlim
  intro n v hv
  apply (hgeometry hH n v hv).mono
  rintro i ⟨hi, hvariance⟩
  have hbound := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hvariance) hK
  exact ⟨hi, (hresponse i).trans (hbound.trans hparameters.2.2)⟩

#print axioms exists_orthonormal_fin
#print axioms finiteDimensional_of_cofinal_small_cuts
#print axioms finiteDimensional_of_cofinal_small_cuts_limit
#print axioms exists_narrow_band_parameters
#print axioms finiteDimensional_of_narrow_band_cuts
#print axioms finiteDimensional_of_narrow_band_limit

end NullCone.Dimension
