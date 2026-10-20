import Erdos940.Quartic.GaussianFiniteConstituentAlignment
import Erdos940.Quartic.GaussianPrimeSumTransfer
import Erdos940.Quartic.GaussianAnyIdealPrimeSum
import Erdos940.Quartic.GaussianSymbolMultiplier
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Uniform prime sums for the nine finite-order quartic constituents
-/

namespace Erdos940.Quartic.GaussianFinitePrimeSumBound

open scoped NumberField
open NumberField IsDedekindDomain
open Erdos940.Quartic
open Erdos940.Quartic.GaussianFiniteConstituentAlignment
open Erdos940.Quartic.GaussianIdealLatticeSeries
open Erdos940.Quartic.GaussianCMConstituentBridge
open Erdos940.Quartic.GaussianAnyIdealPrimeSum
open Erdos940.Quartic.GaussianSymbolMultiplier

/-- The nine finite-order character sums have a uniform `log log D`
bound on the exact good rational-prime set used by the quartic sieve. -/
theorem regular_baseConstituent_finite_quarticBasePrimes_le
    (B : ℕ) (hB : 3 ≤ B)
    (d : Fin 4 → CanonicalParts) (hreg : ¬ ExceptionalTuple d)
    (j : Fin 11) (hj : 1 ≤ j.val ∧ j.val ≤ 9) :
    (∑ p ∈ (quarticBasePrimes B).filter
        (fun p => ∀ i, ¬p ∣ (d i).val),
      baseConstituent d j p / (p : ℝ)) ≤
      Real.log (Real.log (2 * (coefficientProduct d : ℝ))) +
        (Real.log 13 + Real.log (162 + 648 / Real.log 2) +
          6 * Real.log 4 * (1 + 1 / Real.log 2) +
          (2 * (Real.log 4 * (1 + 2 / Real.log 2)) +
            reciprocalSquareConstant) +
          2 * reciprocalSquareConstant) := by
  classical
  let D : ℕ := coefficientProduct d
  let R : ℤ := finiteConstituentRadicand d j
  let F := GaussianIdealExponentVectors.primeBox B
  let T := (quarticBasePrimes B).filter (fun p => ∀ i, ¬p ∣ (d i).val)
  let c : HeightOneSpectrum (𝓞 GaussianField) → ℝ := fun P =>
    (quarticIdealWeight (R : 𝓞 GaussianField)
      gaussianCanonicalFieldEmbedding P.asIdeal).re
  have hD : 0 < D := by
    dsimp [D, coefficientProduct]
    apply Finset.prod_pos
    intro i hi
    exact (d i).property.pos
  have hR0 : R ≠ 0 := finiteConstituentRadicand_ne_zero d hreg j hj
  have hRbound : R.natAbs ≤ D ^ 3 :=
    finiteConstituentRadicand_natAbs_le_cube d j hj
  obtain ⟨b, hb, hsym⟩ :=
    exists_nontrivial_gaussianQuarticIdealSymbol_finiteConstituent
      d hreg j hj
  obtain ⟨a, ha, hunit⟩ :=
    exists_admissible_multiplier_of_symbol_witness R hR0
      gaussianCanonicalFieldEmbedding b hb hsym
  have hc (P : HeightOneSpectrum (𝓞 GaussianField)) (hP : P ∈ F) :
      |c P| ≤ 1 :=
    (Complex.abs_re_le_norm _).trans
      (norm_quarticIdealWeight_le_one (R : 𝓞 GaussianField)
        gaussianCanonicalFieldEmbedding P.asIdeal)
  have hzero (P : HeightOneSpectrum (𝓞 GaussianField))
      (hP : P ∈ F) (hdegree : gaussianDegreeOne P)
      (hbad : Ideal.absNorm P.asIdeal = 2 ∨
        ¬ (∀ i, ¬ Ideal.absNorm P.asIdeal ∣ (d i).val)) : c P = 0 := by
    rcases hbad with htwo | hbad
    · simp only [c, quarticIdealWeight_eq_zero_of_absNorm_two
        (R : 𝓞 GaussianField) gaussianCanonicalFieldEmbedding P htwo,
        Complex.zero_re]
    · obtain ⟨i, hi⟩ := not_forall.mp hbad
      have hpdiv : Ideal.absNorm P.asIdeal ∣ (d i).val := not_not.mp hi
      have hdiv := finiteConstituentRadicand_dvd_of_coefficient_dvd
        d j hj (Ideal.absNorm P.asIdeal) i hpdiv
      simp only [c, quarticIdealWeight_eq_zero_of_prime_dvd_radicand
        (Ideal.absNorm P.asIdeal) R hdiv gaussianCanonicalFieldEmbedding
        P rfl, Complex.zero_re]
  have hsum :
      (∑ p ∈ T, baseConstituent d j p / (p : ℝ)) =
        ∑ P ∈ F.filter (fun P => Ideal.absNorm P.asIdeal ∈ T),
          c P / (Ideal.absNorm P.asIdeal : ℝ) := by
    rw [← gaussianPrimeNormFiberSum_eq_filter F T c]
    apply Finset.sum_congr rfl
    intro p hp
    obtain ⟨hpbase, hgood⟩ := Finset.mem_filter.mp hp
    rw [baseConstituent_finite_eq_primeBox_norm_fiber
      d j hj B p hpbase hgood, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro P hP
    rw [(Finset.mem_filter.mp hP).2]
  have htransfer := gaussianPrime_goodBaseSum_le_full_add_constant
    B (fun p => ∀ i, ¬p ∣ (d i).val) c hc hzero
  have hBreal : (2 : ℝ) ≤ B := by exact_mod_cast (by omega : 2 ≤ B)
  have hlogB : (1 : ℝ) ≤ Real.log (B : ℝ) := by
    have h3 : (1 : ℝ) ≤ Real.log 3 := by
      linarith [Real.log_three_gt_d9]
    exact h3.trans (Real.log_le_log (by norm_num) (by exact_mod_cast hB))
  have hideal := anySignedIdealPrimeSum_le_coefficient_loglog
    F D hD R hR0 hRbound gaussianCanonicalFieldEmbedding a ha hunit
    (B : ℝ) hBreal hlogB
    (GaussianIdealExponentVectors.norm_le_of_mem_primeBox B)
    (fun P => GaussianIdealExponentVectors.norm_gt_of_not_mem_primeBox
      B P.val P.property)
  change (∑ P ∈ F, c P / (Ideal.absNorm P.asIdeal : ℝ)) ≤ _ at hideal
  rw [hsum]
  dsimp [D, F] at hideal
  have hchain := htransfer.trans
    (add_le_add_left hideal reciprocalSquareConstant)
  convert hchain using 1 <;> (simp [F, T] <;> ring)

end Erdos940.Quartic.GaussianFinitePrimeSumBound
