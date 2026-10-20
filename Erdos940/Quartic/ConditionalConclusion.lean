import Erdos940.Quartic.SieveAssembly
import Erdos940.Quartic.DensityBridge

/-!
# Quartic conclusion from the explicit sieve inputs

The theorems here derive positive lower density and coinfinitude of the
quartic complement from the existence of `QuarticSieveProgression` for each
choice of sieve parameters.
-/

namespace Erdos940.Quartic

/-- The quartic sieve estimates give the stronger positive-lower-density
conclusion, not merely infinitely many omissions. -/
theorem positiveLowerDensity_four_of_quartic_sieve_progressions
    (regular : (Fin 4 → CanonicalParts) → Prop)
    (rate : (Fin 4 → CanonicalParts) → ℝ)
    (Creg Cuniv : ℝ) (hCreg : 0 ≤ Creg) (hCuniv : 0 ≤ Cuniv)
    (hrate : ∀ d, 0 < rate d)
    (E₀ : Finset CanonicalParts)
    (hbuild : ∀ (T B : ℕ) (E : Finset CanonicalParts),
      0 < B → E₀ ⊆ E →
        Nonempty (QuarticSieveProgression regular rate Creg Cuniv T B E)) :
    HasPositiveLowerDensityComplementFor 4 := by
  obtain ⟨M, a, hM, ha, hsmall⟩ :=
    exists_quartic_firstMoment_lt_one_eighth regular rate Creg Cuniv
      hCreg hCuniv hrate E₀ hbuild
  letI : NeZero M := ⟨Nat.ne_of_gt hM⟩
  exact positiveLowerDensity_of_firstMoment_limit hM ha hsmall

theorem coinfinite_four_of_quartic_sieve_progressions
    (regular : (Fin 4 → CanonicalParts) → Prop)
    (rate : (Fin 4 → CanonicalParts) → ℝ)
    (Creg Cuniv : ℝ) (hCreg : 0 ≤ Creg) (hCuniv : 0 ≤ Cuniv)
    (hrate : ∀ d, 0 < rate d)
    (E₀ : Finset CanonicalParts)
    (hbuild : ∀ (T B : ℕ) (E : Finset CanonicalParts),
      0 < B → E₀ ⊆ E →
        Nonempty (QuarticSieveProgression regular rate Creg Cuniv T B E)) :
    CoinfiniteFor 4 := by
  obtain ⟨M, a, hM, ha, hsmall⟩ :=
    exists_quartic_firstMoment_lt_one_eighth regular rate Creg Cuniv
      hCreg hCuniv hrate E₀ hbuild
  letI : NeZero M := ⟨Nat.ne_of_gt hM⟩
  exact coinfinite_of_firstMoment_limit hM ha hsmall

end Erdos940.Quartic
