import Erdos940.Quartic.BaseTraceBound
import Erdos940.Quartic.QuarticBaseEstimateConclusion

/-!
# Quartic conclusion reduced to eleven analytic estimates

The intrinsic finite-field trace gives the exact local formula and the
uniform bound unconditionally. The only remaining hypotheses here identify
its eleven constituents and bound their finite prime sums.
-/

namespace Erdos940.Quartic

theorem positiveLowerDensity_four_of_eleven_character_estimates
    (baseConstituent : (Fin 4 → CanonicalParts) → Fin 11 → ℕ → ℝ)
    (error : ℝ)
    (hBaseCharacter : ∀ B, 3 ≤ B → ∀ d, ¬ExceptionalTuple d →
      ∀ p ∈ (quarticBasePrimes B).filter
        (fun p => ∀ i, ¬p ∣ (d i).val),
      quarticBaseTrace d p = ∑ j : Fin 11, baseConstituent d j p)
    (hBaseConstituent : ∀ B, 3 ≤ B → ∀ d, ¬ExceptionalTuple d →
      ∀ j : Fin 11,
      (∑ p ∈ (quarticBasePrimes B).filter
          (fun p => ∀ i, ¬p ∣ (d i).val),
          baseConstituent d j p / (p : ℝ)) ≤
        Real.log (Real.log (2 * (coefficientProduct d : ℝ))) + error) :
    HasPositiveLowerDensityComplementFor 4 := by
  apply positiveLowerDensity_four_of_base_character_estimates
    quarticBaseTrace baseConstituent error
  · intro B hB d p hp
    obtain ⟨hbase, hgood⟩ := Finset.mem_filter.mp hp
    obtain ⟨hIcc, hprime⟩ := Finset.mem_filter.mp hbase
    have hodd : 2 < p := by
      have hthree := (Finset.mem_Icc.mp hIcc).1
      omega
    have hunit : ∀ i, ((d i).val : ZMod p) ≠ 0 := by
      intro i hi
      exact hgood i ((ZMod.natCast_eq_zero_iff (d i).val p).mp hi)
    exact quarticBaseTrace_abs_le_21 d p hprime hodd hunit
  · intro B hB d p hp
    obtain ⟨hbase, _⟩ := Finset.mem_filter.mp hp
    exact quarticBaseTrace_local_density d p (Finset.mem_filter.mp hbase).2
  · exact hBaseCharacter
  · exact hBaseConstituent

end Erdos940.Quartic
