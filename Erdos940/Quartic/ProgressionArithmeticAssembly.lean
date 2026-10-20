import Erdos940.Quartic.ProgressionBuilder
import Erdos940.Quartic.UniformEulerMajorant

/-!
# Arithmetic inputs for the concrete quartic progression

The base-prime trace and its eleven finite character sums imply both the
regular Euler bound and the universal local factor bound. The selected-prime
trace and finite bias remain explicit inputs to this assembly.
-/

namespace Erdos940.Quartic

open Finset

/-- Assemble a quartic sieve progression from finite local traces and
eleven constituent prime-sum estimates. No separate product bounds (15) or
(21) are assumed. -/
noncomputable def quarticSieveProgressionOfFiniteArithmetic
    (rate : (Fin 4 → CanonicalParts) → ℝ)
    (T B : ℕ) (E : Finset CanonicalParts)
    (Q : Finset ℕ) (hB : 3 ≤ B)
    (hQ : ∀ q ∈ Q, q.Prime ∧ 2 < q)
    (hQmod : ∀ q ∈ Q, q % 4 = 3)
    (hfar : ∀ q ∈ Q, B < q)
    (hQbudget : (∑ q ∈ Q, (q : ℝ)⁻¹) ≤ (T : ℝ) + 1)
    (selectedTrace : (Fin 4 → CanonicalParts) → ℕ → ℝ)
    (hSelectedUnit : ∀ d, ¬ExceptionalTuple d → (∀ i, d i ∈ E) →
      ∀ p ∈ Q, ∀ i, ((d i).val : ZMod p) ≠ 0)
    (hSelectedFour : ∀ p ∈ Q, (4 : ZMod p) ≠ 0)
    (hSelectedLocal : ∀ d, ¬ExceptionalTuple d → (∀ i, d i ∈ E) →
      ∀ p ∈ Q,
      (Nat.card {y : Fin 4 → ZMod p //
        (∑ i, ((d i).val : ZMod p) * y i ^ 4) = 0} : ℝ) /
          (p : ℝ) ^ 3 =
          1 + selectedTrace d p * ((p : ℝ)⁻¹ - ((p : ℝ) ^ 2)⁻¹))
    (hSelectedLower : ∀ d, ¬ExceptionalTuple d → (∀ i, d i ∈ E) →
      ∀ p ∈ Q, -(selectedTrace d p) ≤ 1)
    (hSelectedBias : ∀ d, ¬ExceptionalTuple d → (∀ i, d i ∈ E) →
      (∑ p ∈ Q, selectedTrace d p / (p : ℝ)) ≤
        -((T : ℝ) * rate d) + 1)
    (hSelectedSquares : (∑ p ∈ Q, (1 : ℝ) / (p : ℝ) ^ 2) ≤ 1)
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
    QuarticSieveProgression (fun d => ¬ExceptionalTuple d) rate
      (16 * Real.exp (11 * error + 21 * reciprocalSquareConstant))
      quarticUniversalBoundConstant T B E := by
  apply quarticSieveProgressionOfBaseGoodBounds rate
    (16 * Real.exp (11 * error + 21 * reciprocalSquareConstant))
    T B E Q hB hQ hQmod hfar hQbudget selectedTrace
    hSelectedUnit hSelectedFour hSelectedLocal hSelectedLower
    hSelectedBias hSelectedSquares
  · intro d hreg
    exact quarticBaseDensity_le_uniformEuler B Q hQ d
      (baseTrace d) (baseConstituent d) error
      (hBaseTraceBound d) (hBaseLocal d)
      (hBaseCharacter d hreg) (hBaseConstituent d hreg)
  · intro d p hp hgood
    have hpGood : p ∈ (quarticBasePrimes B).filter
        (fun p => ∀ i, ¬p ∣ (d i).val) :=
      Finset.mem_filter.mpr ⟨hp, hgood⟩
    exact quarticBaseGoodFactor_le_exp B p hp d (baseTrace d p)
      hgood (hBaseTraceBound d p hpGood) (hBaseLocal d p hpGood)

end Erdos940.Quartic
