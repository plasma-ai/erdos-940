import Erdos940.Quartic.SelectorIntegration
import Erdos940.Quartic.ProgressionArithmeticAssembly

/-!
# The quartic progression after selected-prime integration

The Chebotarev prime selector and inert local trace now supply all
selected-prime inputs. This theorem exposes the finite base-prime character
estimates that remain for the analytic side of the proof.
-/

namespace Erdos940.Quartic

/-- The fixed positive rate used by the selected-prime construction. -/
noncomputable def quarticFixedBiasRate
    (d : Fin 4 → CanonicalParts) : ℝ :=
  quarticSelectorWeight (coefficientProduct d)

theorem quarticFixedBiasRate_pos
    (d : Fin 4 → CanonicalParts) : 0 < quarticFixedBiasRate d :=
  quarticSelectorWeight_pos _

/-- The concrete quartic sieve progression, conditional only on the
eleven base-prime constituent estimates and their finite local trace
decomposition. -/
noncomputable def quarticSieveProgressionOfBaseCharacterEstimates
    (T B : ℕ) (E : Finset CanonicalParts) (hB : 3 ≤ B)
    (baseTrace : (Fin 4 → CanonicalParts) → ℕ → ℝ)
    (baseConstituent : (Fin 4 → CanonicalParts) → Fin 11 → ℕ → ℝ)
    (error : ℝ)
    (hBaseTraceBound : ∀ d, ∀ p ∈ (quarticBasePrimes B).filter
      (fun p => ∀ i, ¬p ∣ (d i).val), |baseTrace d p| ≤ 21)
    (hBaseLocal : ∀ d, ∀ p ∈ (quarticBasePrimes B).filter
      (fun p => ∀ i, ¬p ∣ (d i).val),
      (Nat.card {y : Fin 4 → ZMod p //
        (∑ i, ((d i).val : ZMod p) * y i ^ 4) = 0} : ℝ) /
          (p : ℝ) ^ 3 =
          1 + baseTrace d p * ((p : ℝ)⁻¹ - ((p : ℝ) ^ 2)⁻¹))
    (hBaseCharacter : ∀ d, ¬ExceptionalTuple d →
      ∀ p ∈ (quarticBasePrimes B).filter
        (fun p => ∀ i, ¬p ∣ (d i).val),
      baseTrace d p = ∑ j : Fin 11, baseConstituent d j p)
    (hBaseConstituent : ∀ d, ¬ExceptionalTuple d →
      ∀ j : Fin 11,
      (∑ p ∈ (quarticBasePrimes B).filter
          (fun p => ∀ i, ¬p ∣ (d i).val),
          baseConstituent d j p / (p : ℝ)) ≤
        Real.log (Real.log (2 * (coefficientProduct d : ℝ))) + error) :
    QuarticSieveProgression (fun d => ¬ExceptionalTuple d)
      quarticFixedBiasRate
      (16 * Real.exp (11 * error + 21 * reciprocalSquareConstant))
      quarticUniversalBoundConstant T B E := by
  let S := Classical.choice (exists_quartic_selected_prime_package T B E)
  exact quarticSieveProgressionOfFiniteArithmetic
    quarticFixedBiasRate T B E S.Q hB S.prime S.inert S.far
    S.budget quarticSelectedTrace S.unit S.four S.trace
    S.traceLower (by
      intro d hreg hd
      simpa [quarticFixedBiasRate, neg_mul] using S.bias d hreg hd)
    S.squares
    baseTrace baseConstituent error hBaseTraceBound hBaseLocal
    hBaseCharacter hBaseConstituent

end Erdos940.Quartic
