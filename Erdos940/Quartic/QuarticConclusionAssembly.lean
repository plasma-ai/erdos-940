import Erdos940.Quartic.ProgressionBuilder
import Erdos940.Quartic.ConditionalConclusion

/-!
# Quartic conclusion assembled from finite local estimates

This is the interface between the analytic selection of auxiliary primes
and the proven counting conclusion. The former supplies a finite set of
selected primes, local trace coefficients and two finite-product bounds
for each requested scale. The CRT progression and final coinfinitude then
follow without another global counting assumption.
-/

namespace Erdos940.Quartic

/-- The finite, problem-specific inputs still needed for one scale of the
quartic sieve. They contain no progression, modulus, or first-moment
assumption; those are constructed downstream. -/
structure QuarticLocalEstimatePackage
    (rate : (Fin 4 → CanonicalParts) → ℝ)
    (Creg : ℝ) (T B : ℕ) (E : Finset CanonicalParts) where
  Q : Finset ℕ
  prime_gt_two : ∀ q ∈ Q, q.Prime ∧ 2 < q
  inert : ∀ q ∈ Q, q % 4 = 3
  far : ∀ q ∈ Q, B < q
  selectedBudget : (∑ q ∈ Q, (q : ℝ)⁻¹) ≤ (T : ℝ) + 1
  A : (Fin 4 → CanonicalParts) → ℕ → ℝ
  unit : ∀ d, ¬ExceptionalTuple d → (∀ i, d i ∈ E) →
    ∀ p ∈ Q, ∀ i, ((d i).val : ZMod p) ≠ 0
  trace : ∀ d, ¬ExceptionalTuple d → (∀ i, d i ∈ E) →
    ∀ p ∈ Q,
      (Nat.card {y : Fin 4 → ZMod p //
        (∑ i, ((d i).val : ZMod p) * y i ^ 4) = 0} : ℝ) /
          (p : ℝ) ^ 3 =
        1 + A d p * ((p : ℝ)⁻¹ - ((p : ℝ) ^ 2)⁻¹)
  traceLower : ∀ d, ¬ExceptionalTuple d → (∀ i, d i ∈ E) →
    ∀ p ∈ Q, -(A d p) ≤ 1
  selectedBias : ∀ d, ¬ExceptionalTuple d → (∀ i, d i ∈ E) →
    (∑ p ∈ Q, A d p / (p : ℝ)) ≤ -((T : ℝ) * rate d) + 1
  reciprocalSquare : (∑ p ∈ Q, (1 : ℝ) / (p : ℝ) ^ 2) ≤ 1
  baseEuler : ∀ d, ¬ExceptionalTuple d →
    quarticBaseDensity B Q prime_gt_two d ≤ Creg *
      (4 : ℝ) ^ (coefficientProduct d).primeFactors.card *
        Real.log (2 * (coefficientProduct d : ℝ)) ^ (11 : ℕ)
  baseGoodFactor : ∀ (d : Fin 4 → CanonicalParts), ∀ p ∈ quarticBasePrimes B,
    (∀ i, ¬p ∣ (d i).val) →
      localDensityFactor (p ^ 2) (fun i => (d i).val) p ≤
        Real.exp (21 / (p : ℝ))

private theorem four_ne_zero_at_selected_prime
    (p : ℕ) (hp : p.Prime) (hodd : 2 < p) :
    (4 : ZMod p) ≠ 0 := by
  intro h
  have hdiv : p ∣ 4 := (ZMod.natCast_eq_zero_iff 4 p).mp h
  have hle : p ≤ 4 := Nat.le_of_dvd (by norm_num) hdiv
  interval_cases p <;> norm_num at *

/-- Construct the sieve progression from local data; oddness of the
selected primes automatically supplies the unit condition on `4`. -/
noncomputable def QuarticLocalEstimatePackage.toProgression
    {rate : (Fin 4 → CanonicalParts) → ℝ}
    {Creg : ℝ} {T B : ℕ} {E : Finset CanonicalParts}
    (D : QuarticLocalEstimatePackage rate Creg T B E)
    (hB : 3 ≤ B) :
    QuarticSieveProgression (fun d => ¬ExceptionalTuple d)
      rate Creg quarticUniversalBoundConstant T B E :=
  quarticSieveProgressionOfLocalBounds rate Creg
    quarticUniversalBoundConstant T B E
    D.Q D.prime_gt_two D.far D.A D.unit
    (fun p hp => four_ne_zero_at_selected_prime p
      (D.prime_gt_two p hp).1 (D.prime_gt_two p hp).2)
    D.trace D.traceLower D.selectedBias D.reciprocalSquare
    D.baseEuler (by
      intro d
      rw [← quarticProgression_density_factorization B D.Q
        D.prime_gt_two D.far]
      exact quarticProgression_density_le_universal B T D.Q hB
        D.prime_gt_two D.inert D.far D.selectedBudget d
        (D.baseGoodFactor d))

/-- The coefficient cutoffs may be chosen with `B≥3`, as required by
the elementary prime-harmonic estimate. -/
private theorem exists_ordered_coefficient_cutoffs_ge_three
    (w c : (Fin 4 → CanonicalParts) → ℝ)
    (hw : Summable w) (hw0 : ∀ d, 0 ≤ w d) (hc : ∀ d, 0 < c d)
    (η : ℝ) (hη0 : 0 < η) (hη : η < 1 / 20)
    (K : ℕ → ℝ) (hK : ∀ T, 0 ≤ K T)
    (E₀ : Finset CanonicalParts) (δ : ℝ) (hδ : 0 < δ) :
    ∃ T B : ℕ, ∃ E : Finset CanonicalParts,
      (∑' d, w d * Real.exp (-((T : ℝ) * c d))) < δ ∧
      3 ≤ B ∧
      K T * Real.log (2 * (B : ℝ)) ^ (30 : ℕ) *
        (∑' d : Fin 4 → CanonicalParts,
          if ∃ p ∈ (coefficientProduct d).primeFactors, B < p then
            coefficientOmegaWeight d else 0) < δ ∧
      E₀ ⊆ E ∧
      K T * Real.log (2 * (B : ℝ)) ^ (30 : ℕ) *
        (∑' d : Fin 4 → CanonicalParts,
          if ∀ i, d i ∈ E then 0 else coefficientOmegaWeight d) < δ := by
  classical
  obtain ⟨T₀, hT₀⟩ :=
    exists_nat_forall_ge_tsum_weight_mul_exp_neg_lt w c hw hw0 hc hδ
  let T := T₀
  have hT := hT₀ T (le_refl T)
  obtain ⟨B₀, hB₀⟩ := exists_primeCutoff_tail_log_bound η hη0 hη
    (K T) δ (hK T) hδ
  let B := max B₀ 3
  obtain ⟨_, hBtail⟩ := hB₀ B (le_max_left _ _)
  have hB : 3 ≤ B := le_max_right B₀ 3
  have hlog : 0 ≤ Real.log (2 * (B : ℝ)) := by
    apply Real.log_nonneg
    have hBr : (3 : ℝ) ≤ B := by exact_mod_cast hB
    linarith
  obtain ⟨E, hE, hEtail⟩ :=
    exists_coefficientOmegaWeight_finite_family_tail_lt E₀
      (K T * Real.log (2 * (B : ℝ)) ^ (30 : ℕ)) δ
      (mul_nonneg (hK T) (pow_nonneg hlog _)) hδ
  exact ⟨T, B, E, hT, hB, hBtail, hE, hEtail⟩

/-- With `B≥3` available, the first-moment cutoff argument applies to
the concrete local-estimate package rather than an assumed progression. -/
private theorem exists_quartic_firstMoment_of_local_estimates
    (rate : (Fin 4 → CanonicalParts) → ℝ)
    (Creg : ℝ) (hCreg : 0 ≤ Creg)
    (hrate : ∀ d, 0 < rate d)
    (E₀ : Finset CanonicalParts)
    (hlocal : ∀ (T B : ℕ) (E : Finset CanonicalParts),
      3 ≤ B → E₀ ⊆ E →
        Nonempty (QuarticLocalEstimatePackage rate Creg T B E)) :
    ∃ M a : ℕ, ∃ hM : 0 < M,
      a < M ∧
      (letI : NeZero M := ⟨Nat.ne_of_gt hM⟩
       (∑' d : Fin 4 → CanonicalParts,
         fixedPartVolume (fun i => (d i).val) *
           (localCount (fun i => (d i).val) M a : ℝ) / (M : ℝ) ^ 4) <
         1 / (8 * (M : ℝ))) := by
  classical
  have hwsum := summable_regularSieveWeight
    (fun d => ¬ExceptionalTuple d) Creg hCreg
  let V : ℝ := Real.Gamma (5 / 4 : ℝ) ^ 4
  let K : ℕ → ℝ := fun T =>
    V * quarticUniversalBoundConstant * Real.exp ((T : ℝ) + 1)
  have hCuniv : 0 ≤ quarticUniversalBoundConstant := by
    unfold quarticUniversalBoundConstant
    positivity
  have hK : ∀ T, 0 ≤ K T := by
    intro T
    dsimp [K, V]
    positivity
  obtain ⟨T, B, E, hT, hB, hBtail, hEsub, hEtail⟩ :=
    exists_ordered_coefficient_cutoffs_ge_three
      (regularSieveWeight (fun d => ¬ExceptionalTuple d) Creg)
      rate hwsum
      (regularSieveWeight_nonneg _ Creg hCreg) hrate
      (1 / 40 : ℝ) (by norm_num) (by norm_num)
      K hK E₀ (1 / 32 : ℝ) (by norm_num)
  obtain ⟨D⟩ := hlocal T B E hB hEsub
  let S := D.toProgression hB
  have hBpos : 0 < B := by omega
  have hB' : (Real.Gamma (5 / 4 : ℝ) ^ 4 *
      quarticUniversalBoundConstant * Real.exp ((T : ℝ) + 1)) *
      Real.log (2 * (B : ℝ)) ^ (30 : ℕ) *
        (∑' d : Fin 4 → CanonicalParts,
          if ∃ p ∈ (coefficientProduct d).primeFactors, B < p then
            coefficientOmegaWeight d else 0) < 1 / 32 := by
    simpa only [K, V] using hBtail
  have hE' : (Real.Gamma (5 / 4 : ℝ) ^ 4 *
      quarticUniversalBoundConstant * Real.exp ((T : ℝ) + 1)) *
      Real.log (2 * (B : ℝ)) ^ (30 : ℕ) *
        (∑' d : Fin 4 → CanonicalParts,
          if ∀ i, d i ∈ E then 0 else coefficientOmegaWeight d) < 1 / 32 := by
    simpa only [K, V] using hEtail
  obtain ⟨hsum, hglob⟩ := S.global_bound hCreg hCuniv hBpos
    hrate hwsum hT hB' hE'
  letI : NeZero S.M := ⟨Nat.ne_of_gt S.Mpos⟩
  refine ⟨S.M, S.a, S.Mpos, S.aLt, ?_⟩
  have hsmall :
      (∑' d : Fin 4 → CanonicalParts,
        Real.Gamma (5 / 4 : ℝ) ^ 4 * coefficientWeight d *
          normalizedQuarticLocalDensity S.M S.a d) < 1 / 8 := by
    have hnumeric : (3 : ℝ) * (1 / 32) < 1 / 8 := by norm_num
    exact hglob.trans hnumeric
  have hMreal : 0 < (S.M : ℝ) := by exact_mod_cast S.Mpos
  rw [firstMoment_eq_normalized_div S.M S.a S.Mpos hsum]
  have hdiv := div_lt_div_of_pos_right hsmall hMreal
  convert hdiv using 1 <;> ring

/-- The quartic conclusion from explicit local estimates at every
selected scale. The stronger positive-lower-density assertion is retained. -/
theorem positiveLowerDensity_four_of_quartic_local_estimates
    (rate : (Fin 4 → CanonicalParts) → ℝ)
    (Creg : ℝ) (hCreg : 0 ≤ Creg)
    (hrate : ∀ d, 0 < rate d)
    (E₀ : Finset CanonicalParts)
    (hlocal : ∀ (T B : ℕ) (E : Finset CanonicalParts),
      3 ≤ B → E₀ ⊆ E →
        Nonempty (QuarticLocalEstimatePackage rate Creg T B E)) :
    HasPositiveLowerDensityComplementFor 4 := by
  obtain ⟨M, a, hM, ha, hsmall⟩ :=
    exists_quartic_firstMoment_of_local_estimates
      rate Creg hCreg hrate E₀ hlocal
  letI : NeZero M := ⟨Nat.ne_of_gt hM⟩
  exact positiveLowerDensity_of_firstMoment_limit hM ha hsmall

theorem coinfinite_four_of_quartic_local_estimates
    (rate : (Fin 4 → CanonicalParts) → ℝ)
    (Creg : ℝ) (hCreg : 0 ≤ Creg)
    (hrate : ∀ d, 0 < rate d)
    (E₀ : Finset CanonicalParts)
    (hlocal : ∀ (T B : ℕ) (E : Finset CanonicalParts),
      3 ≤ B → E₀ ⊆ E →
        Nonempty (QuarticLocalEstimatePackage rate Creg T B E)) :
    CoinfiniteFor 4 :=
  coinfiniteFor_of_positiveLowerDensity
    (positiveLowerDensity_four_of_quartic_local_estimates
      rate Creg hCreg hrate E₀ hlocal)

end Erdos940.Quartic
