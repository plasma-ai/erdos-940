import Erdos940.Quartic.SelectorProgressionAssembly
import Erdos940.Quartic.QuarticConclusionAssembly

/-!
# Positive lower density from base-prime character estimates

The selected-prime inputs are supplied by the finite Chebotarev construction.
Four finite base-prime estimates, uniform over cutoffs `B ≥ 3`, imply positive
lower density of the quartic complement.
-/

namespace Erdos940.Quartic

/-- If the base-prime trace admits the prescribed eleven-character
decomposition and uniform prime-sum bounds, the complement of sums of
four 4-powerful numbers has positive lower density. -/
theorem positiveLowerDensity_four_of_base_character_estimates
    (baseTrace : (Fin 4 → CanonicalParts) → ℕ → ℝ)
    (baseConstituent : (Fin 4 → CanonicalParts) → Fin 11 → ℕ → ℝ)
    (error : ℝ)
    (hBaseTraceBound : ∀ B, 3 ≤ B → ∀ d, ∀ p ∈
      (quarticBasePrimes B).filter (fun p => ∀ i, ¬p ∣ (d i).val),
      |baseTrace d p| ≤ 21)
    (hBaseLocal : ∀ B, 3 ≤ B → ∀ d, ∀ p ∈
      (quarticBasePrimes B).filter (fun p => ∀ i, ¬p ∣ (d i).val),
      (Nat.card {y : Fin 4 → ZMod p //
        (∑ i, ((d i).val : ZMod p) * y i ^ 4) = 0} : ℝ) /
          (p : ℝ) ^ 3 =
          1 + baseTrace d p * ((p : ℝ)⁻¹ - ((p : ℝ) ^ 2)⁻¹))
    (hBaseCharacter : ∀ B, 3 ≤ B → ∀ d, ¬ExceptionalTuple d →
      ∀ p ∈ (quarticBasePrimes B).filter
        (fun p => ∀ i, ¬p ∣ (d i).val),
      baseTrace d p = ∑ j : Fin 11, baseConstituent d j p)
    (hBaseConstituent : ∀ B, 3 ≤ B → ∀ d, ¬ExceptionalTuple d →
      ∀ j : Fin 11,
      (∑ p ∈ (quarticBasePrimes B).filter
          (fun p => ∀ i, ¬p ∣ (d i).val),
          baseConstituent d j p / (p : ℝ)) ≤
        Real.log (Real.log (2 * (coefficientProduct d : ℝ))) + error) :
    HasPositiveLowerDensityComplementFor 4 := by
  let Creg : ℝ := 16 * Real.exp
    (11 * error + 21 * reciprocalSquareConstant)
  have hCreg : 0 ≤ Creg := by dsimp [Creg]; positivity
  apply positiveLowerDensity_four_of_quartic_local_estimates
    quarticFixedBiasRate Creg hCreg quarticFixedBiasRate_pos ∅
  intro T B E hB hE
  let S := Classical.choice (exists_quartic_selected_prime_package T B E)
  refine ⟨{
    Q := S.Q
    prime_gt_two := S.prime
    inert := S.inert
    far := S.far
    selectedBudget := S.budget
    A := quarticSelectedTrace
    unit := S.unit
    trace := S.trace
    traceLower := S.traceLower
    selectedBias := ?_
    reciprocalSquare := S.squares
    baseEuler := ?_
    baseGoodFactor := ?_
  }⟩
  · intro d hreg hd
    simpa [quarticFixedBiasRate, neg_mul] using S.bias d hreg hd
  · intro d hreg
    exact quarticBaseDensity_le_uniformEuler B S.Q S.prime d
      (baseTrace d) (baseConstituent d) error
      (hBaseTraceBound B hB d) (hBaseLocal B hB d)
      (hBaseCharacter B hB d hreg)
      (hBaseConstituent B hB d hreg)
  · intro d p hp hgood
    have hpGood : p ∈ (quarticBasePrimes B).filter
        (fun p => ∀ i, ¬p ∣ (d i).val) :=
      Finset.mem_filter.mpr ⟨hp, hgood⟩
    exact quarticBaseGoodFactor_le_exp B p hp d (baseTrace d p)
      hgood (hBaseTraceBound B hB d p hpGood)
      (hBaseLocal B hB d p hpGood)

end Erdos940.Quartic
