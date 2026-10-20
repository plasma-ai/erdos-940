import Erdos940.Quartic.CoefficientCutoffs
import Erdos940.Quartic.VolumeConstant

/-!
# Abstract quartic sieve assembly

The arithmetic inputs are a small-modulus Euler bound (15), a selected-prime
decay bound (20), a universal bound (21), and exact elimination (8) of
exceptional tuples supported below the cutoff. Once those pointwise inputs
are supplied, this module chooses parameters in the order `T`, `B`, `E`,
then the progression, and controls the complete coefficient sum.
-/

namespace Erdos940.Quartic

open Filter
open scoped Topology

private theorem coefficientProduct_pos' (d : Fin 4 → CanonicalParts) :
    0 < coefficientProduct d := by
  unfold coefficientProduct
  exact Finset.prod_pos (fun i _ => CanonicalPart.pos (d i).property)

private theorem coefficientWeight_mul_omega_eq (d : Fin 4 → CanonicalParts) :
    coefficientWeight d * (4 : ℝ) ^ (coefficientProduct d).primeFactors.card =
      coefficientOmegaWeight d := by
  have hprod : (coefficientProduct d : ℝ) ^ (-(1 / 4 : ℝ)) =
      coefficientWeight d := by
    unfold coefficientProduct coefficientWeight
    rw [Nat.cast_prod]
    exact (Real.finsetProd_rpow _ _ (by
      intro i hi
      have hdi : 0 < (d i).val := CanonicalPart.pos (d i).property
      exact_mod_cast hdi.le) _).symm
  unfold coefficientOmegaWeight
  rw [hprod]
  ring

private theorem log_two_coefficientProduct_nonneg (d : Fin 4 → CanonicalParts) :
    0 ≤ Real.log (2 * (coefficientProduct d : ℝ)) := by
  apply Real.log_nonneg
  have hD : (1 : ℝ) ≤ (coefficientProduct d : ℝ) := by
    exact_mod_cast (coefficientProduct_pos' d)
  linarith

/-- Normalized local density `ρ_M(a;d)`. -/
noncomputable def normalizedQuarticLocalDensity (M a : ℕ)
    (d : Fin 4 → CanonicalParts) : ℝ :=
  if hM : M = 0 then 0 else
    letI : NeZero M := ⟨hM⟩
    (localCount (fun i => (d i).val) M a : ℝ) / (M : ℝ) ^ 3

theorem normalizedQuarticLocalDensity_nonneg (M a : ℕ)
    (d : Fin 4 → CanonicalParts) :
    0 ≤ normalizedQuarticLocalDensity M a d := by
  unfold normalizedQuarticLocalDensity
  split_ifs <;> positivity

/-- The damping weight in (22), including the fixed regular Euler constant
and the quartic volume. Its summability is a consequence of the coefficient
majorant and `log(2D)¹¹ = O(D^η)`, and is exposed as a separate analytic input
to the assembly theorem. -/
noncomputable def regularSieveWeight
    (regular : (Fin 4 → CanonicalParts) → Prop) (Creg : ℝ)
    (d : Fin 4 → CanonicalParts) : ℝ := by
  classical
  exact if regular d then
    Real.Gamma (5 / 4 : ℝ) ^ 4 * Creg * Real.exp 2 *
      coefficientOmegaWeight d *
        Real.log (2 * (coefficientProduct d : ℝ)) ^ (11 : ℕ)
    else 0

theorem regularSieveWeight_nonneg
    (regular : (Fin 4 → CanonicalParts) → Prop) (Creg : ℝ)
    (hCreg : 0 ≤ Creg) (d : Fin 4 → CanonicalParts) :
    0 ≤ regularSieveWeight regular Creg d := by
  classical
  unfold regularSieveWeight
  split_ifs
  · have hV : 0 ≤ Real.Gamma (5 / 4 : ℝ) ^ 4 := by
      exact pow_nonneg (Real.Gamma_pos_of_pos (by norm_num)).le _
    have hOmega : 0 ≤ coefficientOmegaWeight d := by
      unfold coefficientOmegaWeight
      positivity
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg hV hCreg) (Real.exp_pos _).le) hOmega)
      (pow_nonneg (log_two_coefficientProduct_nonneg d) _)
  · exact le_refl _

private theorem log_two_coefficientProduct_pow_le (η : ℝ) (hη : 0 < η)
    (d : Fin 4 → CanonicalParts) :
    Real.log (2 * (coefficientProduct d : ℝ)) ^ (11 : ℕ) ≤
      (((η / 11)⁻¹) ^ (11 : ℕ) * (2 : ℝ) ^ η) *
        (coefficientProduct d : ℝ) ^ η := by
  let D : ℝ := (coefficientProduct d : ℝ)
  have hD : 0 < D := by
    dsimp [D]
    exact_mod_cast coefficientProduct_pos' d
  have hε : 0 < η / 11 := by positivity
  have hlog := Real.log_le_rpow_div
    (show 0 ≤ 2 * D by positivity) hε
  have hpow := pow_le_pow_left₀
    (log_two_coefficientProduct_nonneg d) hlog 11
  calc
    Real.log (2 * (coefficientProduct d : ℝ)) ^ (11 : ℕ)
        ≤ ((2 * D) ^ (η / 11) / (η / 11)) ^ (11 : ℕ) := hpow
    _ = (((η / 11)⁻¹) ^ (11 : ℕ) * (2 : ℝ) ^ η) * D ^ η := by
      rw [div_eq_mul_inv, mul_pow,
        ← Real.rpow_mul_natCast (show 0 ≤ 2 * D by positivity) (η / 11) 11]
      have he : η / 11 * (11 : ℝ) = η := by ring
      rw [show (↑(11 : ℕ) : ℝ) = 11 by norm_num, he,
        Real.mul_rpow (by norm_num) hD.le]
      ring

/-- The logarithmic regular weight in (22) is summable, for any regularity
predicate. This discharges the analytic premise using the `η < 1/20`
coefficient majorant. -/
theorem summable_regularSieveWeight
    (regular : (Fin 4 → CanonicalParts) → Prop)
    (Creg : ℝ) (hCreg : 0 ≤ Creg) :
    Summable (regularSieveWeight regular Creg) := by
  classical
  let η : ℝ := 1 / 40
  have hη0 : 0 < η := by dsimp [η]; norm_num
  have hη : η < 1 / 20 := by dsimp [η]; norm_num
  let A : ℝ := Real.Gamma (5 / 4 : ℝ) ^ 4 * Creg * Real.exp 2 *
    (((η / 11)⁻¹) ^ (11 : ℕ) * (2 : ℝ) ^ η)
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hbound (d : Fin 4 → CanonicalParts) :
      regularSieveWeight regular Creg d ≤ A *
        ((4 : ℝ) ^ (coefficientProduct d).primeFactors.card *
          (coefficientProduct d : ℝ) ^ (-(1 / 4 : ℝ) + η)) := by
    by_cases hr : regular d
    · have hlog := log_two_coefficientProduct_pow_le η hη0 d
      have hpre : 0 ≤ Real.Gamma (5 / 4 : ℝ) ^ 4 * Creg * Real.exp 2 *
          coefficientOmegaWeight d := by
        unfold coefficientOmegaWeight
        positivity
      have hstep := mul_le_mul_of_nonneg_left hlog hpre
      have hD : 0 < (coefficientProduct d : ℝ) := by
        exact_mod_cast coefficientProduct_pos' d
      unfold coefficientOmegaWeight at hstep
      simp only [regularSieveWeight, if_pos hr, A, coefficientOmegaWeight]
      have hpowD : (coefficientProduct d : ℝ) ^ (-(1 / 4 : ℝ)) *
          (coefficientProduct d : ℝ) ^ η =
          (coefficientProduct d : ℝ) ^ (-(1 / 4 : ℝ) + η) := by
        rw [← Real.rpow_add hD]
      apply hstep.trans_eq
      calc
        _ = (Real.Gamma (5 / 4 : ℝ) ^ 4 * Creg * Real.exp 2 *
            (((η / 11)⁻¹) ^ (11 : ℕ) * (2 : ℝ) ^ η)) *
            ((4 : ℝ) ^ (coefficientProduct d).primeFactors.card *
              ((coefficientProduct d : ℝ) ^ (-(1 / 4 : ℝ)) *
                (coefficientProduct d : ℝ) ^ η)) := by ring
        _ = _ := by rw [hpowD]
    · have hr0 : regularSieveWeight regular Creg d = 0 := by
        simp only [regularSieveWeight, if_neg hr]
      rw [hr0]
      positivity
  apply Summable.of_nonneg_of_le
    (regularSieveWeight_nonneg regular Creg hCreg)
    hbound
  exact (summable_coefficientOmegaWeight_eta η hη).mul_left A

/-- The local statements supplied after the parameters have been chosen.
`baseDensity` is the small-prime factor, and `selectedDensity` is the
selected-prime factor. The hypotheses name (15), (20), (21), and (8)
separately; none is a global first-moment assumption. -/
structure QuarticSieveProgression
    (regular : (Fin 4 → CanonicalParts) → Prop)
    (rate : (Fin 4 → CanonicalParts) → ℝ)
    (Creg Cuniv : ℝ) (T B : ℕ) (E : Finset CanonicalParts) where
  M : ℕ
  a : ℕ
  Mpos : 0 < M
  aLt : a < M
  baseDensity : (Fin 4 → CanonicalParts) → ℝ
  selectedDensity : (Fin 4 → CanonicalParts) → ℝ
  base_nonneg : ∀ d, 0 ≤ baseDensity d
  selected_nonneg : ∀ d, 0 ≤ selectedDensity d
  density_factorization : ∀ d,
    normalizedQuarticLocalDensity M a d = baseDensity d * selectedDensity d
  bound15 : ∀ d, regular d →
    baseDensity d ≤ Creg *
      (4 : ℝ) ^ (coefficientProduct d).primeFactors.card *
        Real.log (2 * (coefficientProduct d : ℝ)) ^ (11 : ℕ)
  bound20 : ∀ d, regular d → (∀ i, d i ∈ E) →
    selectedDensity d ≤ Real.exp (-((T : ℝ) * rate d) + 2)
  bound21 : ∀ d,
    normalizedQuarticLocalDensity M a d ≤
      Cuniv * Real.exp ((T : ℝ) + 1) *
        Real.log (2 * (B : ℝ)) ^ (30 : ℕ) *
          (4 : ℝ) ^ (coefficientProduct d).primeFactors.card
  exceptional_zero8 : ∀ d, ¬regular d →
    (¬∃ p ∈ (coefficientProduct d).primeFactors, B < p) →
      normalizedQuarticLocalDensity M a d = 0

private theorem summable_and_tsum_lt_three_of_pointwise
    {ι : Type*} (f g₁ g₂ g₃ : ι → ℝ)
    (hf0 : ∀ i, 0 ≤ f i)
    (hg₁ : Summable g₁) (hg₂ : Summable g₂) (hg₃ : Summable g₃)
    (hpoint : ∀ i, f i ≤ g₁ i + g₂ i + g₃ i)
    {δ : ℝ} (h₁ : (∑' i, g₁ i) < δ)
    (h₂ : (∑' i, g₂ i) < δ) (h₃ : (∑' i, g₃ i) < δ) :
    Summable f ∧ (∑' i, f i) < 3 * δ := by
  have hgsum : Summable (fun i => g₁ i + g₂ i + g₃ i) :=
    (hg₁.add hg₂).add hg₃
  have hf : Summable f := Summable.of_nonneg_of_le hf0 hpoint hgsum
  have hle := hf.tsum_le_tsum hpoint hgsum
  rw [(hg₁.add hg₂).tsum_add hg₃, hg₁.tsum_add hg₂] at hle
  exact ⟨hf, by linarith⟩

private theorem summable_coefficientOmegaWeight_indicator
    (P : (Fin 4 → CanonicalParts) → Prop) [DecidablePred P] :
    Summable (fun d => if P d then coefficientOmegaWeight d else 0) := by
  classical
  apply Summable.of_nonneg_of_le
    (fun d => by
      split_ifs
      · unfold coefficientOmegaWeight
        positivity
      · exact le_refl _)
    (fun d => by
      split_ifs
      · exact le_refl _
      · unfold coefficientOmegaWeight
        positivity)
  exact summable_coefficientOmegaWeight

/-- The global normalized first moment is at most the sum of the three
cutoff errors. No hypothesis here bounds the global sum directly. -/
theorem QuarticSieveProgression.global_bound
    {regular : (Fin 4 → CanonicalParts) → Prop}
    {rate : (Fin 4 → CanonicalParts) → ℝ}
    {Creg Cuniv : ℝ} {T B : ℕ} {E : Finset CanonicalParts}
    (S : QuarticSieveProgression regular rate Creg Cuniv T B E)
    (hCreg : 0 ≤ Creg) (hCuniv : 0 ≤ Cuniv)
    (hBpos : 0 < B)
    (hrate : ∀ d, 0 < rate d)
    (hwsum : Summable (regularSieveWeight regular Creg))
    {δ : ℝ}
    (hT : (∑' d, regularSieveWeight regular Creg d *
      Real.exp (-((T : ℝ) * rate d))) < δ)
    (hB : (Real.Gamma (5 / 4 : ℝ) ^ 4 * Cuniv *
      Real.exp ((T : ℝ) + 1)) * Real.log (2 * (B : ℝ)) ^ (30 : ℕ) *
        (∑' d : Fin 4 → CanonicalParts,
          if ∃ p ∈ (coefficientProduct d).primeFactors, B < p then
            coefficientOmegaWeight d else 0) < δ)
    (hE : (Real.Gamma (5 / 4 : ℝ) ^ 4 * Cuniv *
      Real.exp ((T : ℝ) + 1)) * Real.log (2 * (B : ℝ)) ^ (30 : ℕ) *
        (∑' d : Fin 4 → CanonicalParts,
          if ∀ i, d i ∈ E then 0 else coefficientOmegaWeight d) < δ) :
    Summable (fun d : Fin 4 → CanonicalParts =>
      Real.Gamma (5 / 4 : ℝ) ^ 4 * coefficientWeight d *
        normalizedQuarticLocalDensity S.M S.a d) ∧
      (∑' d : Fin 4 → CanonicalParts,
        Real.Gamma (5 / 4 : ℝ) ^ 4 * coefficientWeight d *
          normalizedQuarticLocalDensity S.M S.a d) < 3 * δ := by
  classical
  let V : ℝ := Real.Gamma (5 / 4 : ℝ) ^ 4
  let L : ℝ := V * Cuniv * Real.exp ((T : ℝ) + 1) *
    Real.log (2 * (B : ℝ)) ^ (30 : ℕ)
  let f : (Fin 4 → CanonicalParts) → ℝ := fun d =>
    V * coefficientWeight d * normalizedQuarticLocalDensity S.M S.a d
  let g₁ : (Fin 4 → CanonicalParts) → ℝ := fun d =>
    regularSieveWeight regular Creg d * Real.exp (-((T : ℝ) * rate d))
  let g₂ : (Fin 4 → CanonicalParts) → ℝ := fun d =>
    L * (if ∃ p ∈ (coefficientProduct d).primeFactors, B < p then
      coefficientOmegaWeight d else 0)
  let g₃ : (Fin 4 → CanonicalParts) → ℝ := fun d =>
    L * (if ∀ i, d i ∈ E then 0 else coefficientOmegaWeight d)
  have hV : 0 ≤ V := by
    dsimp [V]
    exact pow_nonneg (Real.Gamma_pos_of_pos (by norm_num)).le _
  have hlogB : 0 ≤ Real.log (2 * (B : ℝ)) := by
    apply Real.log_nonneg
    have hBr : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hBpos
    linarith
  have hL : 0 ≤ L := by
    dsimp [L]
    positivity
  have hf0 (d : Fin 4 → CanonicalParts) : 0 ≤ f d := by
    dsimp [f]
    exact mul_nonneg (mul_nonneg hV (coefficientWeight_nonneg d))
      (normalizedQuarticLocalDensity_nonneg S.M S.a d)
  have hg₁ : Summable g₁ := by
    apply Summable.of_nonneg_of_le
      (fun d => by
        dsimp [g₁]
        exact mul_nonneg
          (regularSieveWeight_nonneg regular Creg hCreg d) (Real.exp_pos _).le)
      (fun d => by
        dsimp [g₁]
        have harg : -((T : ℝ) * rate d) ≤ 0 := by
          exact neg_nonpos.mpr (mul_nonneg (Nat.cast_nonneg _) (hrate d).le)
        have hexp : Real.exp (-((T : ℝ) * rate d)) ≤ 1 := by
          simpa using (Real.exp_le_exp.mpr harg)
        exact mul_le_of_le_one_right
          (regularSieveWeight_nonneg regular Creg hCreg d) hexp)
    exact hwsum
  have hp : Summable (fun d : Fin 4 → CanonicalParts =>
      if ∃ p ∈ (coefficientProduct d).primeFactors, B < p then
        coefficientOmegaWeight d else 0) :=
    summable_coefficientOmegaWeight_indicator _
  have he : Summable (fun d : Fin 4 → CanonicalParts =>
      if ∀ i, d i ∈ E then 0 else coefficientOmegaWeight d) := by
    have h := summable_coefficientOmegaWeight_indicator
      (fun d : Fin 4 → CanonicalParts => ¬∀ i, d i ∈ E)
    exact h.congr (fun d => by
      by_cases hd : ∀ i, d i ∈ E <;> simp [hd])
  have hg₂ : Summable g₂ := hp.mul_left L
  have hg₃ : Summable g₃ := he.mul_left L
  have h₂ : (∑' d, g₂ d) < δ := by
    change (∑' d, L *
      (if ∃ p ∈ (coefficientProduct d).primeFactors, B < p then
        coefficientOmegaWeight d else 0)) < δ
    rw [hp.tsum_mul_left]
    exact hB
  have h₃ : (∑' d, g₃ d) < δ := by
    change (∑' d, L *
      (if ∀ i, d i ∈ E then 0 else coefficientOmegaWeight d)) < δ
    rw [he.tsum_mul_left]
    exact hE
  have hreg_bound (d : Fin 4 → CanonicalParts)
      (hr : regular d) (hdE : ∀ i, d i ∈ E) : f d ≤ g₁ d := by
    have hbase := S.bound15 d hr
    have hselected := S.bound20 d hr hdE
    have hbase_upper_nonneg : 0 ≤ Creg *
        (4 : ℝ) ^ (coefficientProduct d).primeFactors.card *
          Real.log (2 * (coefficientProduct d : ℝ)) ^ (11 : ℕ) := by
      exact mul_nonneg
        (mul_nonneg hCreg (by positivity))
        (pow_nonneg (log_two_coefficientProduct_nonneg d) _)
    have hρ : normalizedQuarticLocalDensity S.M S.a d ≤
        (Creg * (4 : ℝ) ^ (coefficientProduct d).primeFactors.card *
          Real.log (2 * (coefficientProduct d : ℝ)) ^ (11 : ℕ)) *
          Real.exp (-((T : ℝ) * rate d) + 2) := by
      rw [S.density_factorization d]
      exact mul_le_mul hbase hselected (S.selected_nonneg d) hbase_upper_nonneg
    calc
      f d ≤ V * coefficientWeight d *
          ((Creg * (4 : ℝ) ^ (coefficientProduct d).primeFactors.card *
            Real.log (2 * (coefficientProduct d : ℝ)) ^ (11 : ℕ)) *
            Real.exp (-((T : ℝ) * rate d) + 2)) := by
          exact mul_le_mul_of_nonneg_left hρ
            (mul_nonneg hV (coefficientWeight_nonneg d))
      _ = g₁ d := by
        dsimp [g₁, regularSieveWeight]
        simp only [if_pos hr, Real.exp_add]
        rw [← coefficientWeight_mul_omega_eq d]
        ring
  have huniv_bound (d : Fin 4 → CanonicalParts) :
      f d ≤ L * coefficientOmegaWeight d := by
    have hρ := S.bound21 d
    calc
      f d ≤ V * coefficientWeight d *
          (Cuniv * Real.exp ((T : ℝ) + 1) *
            Real.log (2 * (B : ℝ)) ^ (30 : ℕ) *
              (4 : ℝ) ^ (coefficientProduct d).primeFactors.card) := by
          exact mul_le_mul_of_nonneg_left hρ
            (mul_nonneg hV (coefficientWeight_nonneg d))
      _ = L * coefficientOmegaWeight d := by
        dsimp [L]
        rw [← coefficientWeight_mul_omega_eq d]
        ring
  have hpoint (d : Fin 4 → CanonicalParts) :
      f d ≤ g₁ d + g₂ d + g₃ d := by
    have hg₁0 : 0 ≤ g₁ d := by
      dsimp [g₁]
      exact mul_nonneg
        (regularSieveWeight_nonneg regular Creg hCreg d) (Real.exp_pos _).le
    have hg₂0 : 0 ≤ g₂ d := by
      dsimp [g₂]
      apply mul_nonneg hL
      split_ifs
      · unfold coefficientOmegaWeight
        positivity
      · exact le_refl _
    have hg₃0 : 0 ≤ g₃ d := by
      dsimp [g₃]
      apply mul_nonneg hL
      split_ifs
      · exact le_refl _
      · unfold coefficientOmegaWeight
        positivity
    by_cases hdE : ∀ i, d i ∈ E
    · by_cases hr : regular d
      · linarith [hreg_bound d hr hdE]
      · by_cases hp : ∃ p ∈ (coefficientProduct d).primeFactors, B < p
        · have hg₂eq : g₂ d = L * coefficientOmegaWeight d := by
            simp only [g₂, hp, ↓reduceIte]
          linarith [huniv_bound d]
        · have hz := S.exceptional_zero8 d hr hp
          have hfzero : f d = 0 := by simp [f, hz]
          linarith
    · have hg₃eq : g₃ d = L * coefficientOmegaWeight d := by
        simp [g₃, hdE]
      linarith [huniv_bound d]
  simpa only [f, V, g₁] using
    summable_and_tsum_lt_three_of_pointwise f g₁ g₂ g₃
      hf0 hg₁ hg₂ hg₃ hpoint hT h₂ h₃

/-- Conversion from the normalized local density to the exact first-moment
constant used by `DensityBridge`. -/
theorem firstMoment_eq_normalized_div (M a : ℕ) [NeZero M] (hM : 0 < M)
    (hsum : Summable (fun d : Fin 4 → CanonicalParts =>
      Real.Gamma (5 / 4 : ℝ) ^ 4 * coefficientWeight d *
        normalizedQuarticLocalDensity M a d)) :
    (∑' d : Fin 4 → CanonicalParts,
      fixedPartVolume (fun i => (d i).val) *
        (localCount (fun i => (d i).val) M a : ℝ) / (M : ℝ) ^ 4) =
      (∑' d : Fin 4 → CanonicalParts,
        Real.Gamma (5 / 4 : ℝ) ^ 4 * coefficientWeight d *
          normalizedQuarticLocalDensity M a d) / (M : ℝ) := by
  have hMne : (M : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
  have hterm (d : Fin 4 → CanonicalParts) :
      fixedPartVolume (fun i => (d i).val) *
        (localCount (fun i => (d i).val) M a : ℝ) / (M : ℝ) ^ 4 =
      (Real.Gamma (5 / 4 : ℝ) ^ 4 * coefficientWeight d *
        normalizedQuarticLocalDensity M a d) / (M : ℝ) := by
    rw [fixedPartVolume_eq_gamma_weight (fun i => (d i).val)
      (fun i => (d i).property.pos)]
    change _ = _
    unfold normalizedQuarticLocalDensity
    rw [dif_neg (Nat.ne_of_gt hM)]
    field_simp
    unfold coefficientWeight
    ring
  calc
    (∑' d : Fin 4 → CanonicalParts,
      fixedPartVolume (fun i => (d i).val) *
        (localCount (fun i => (d i).val) M a : ℝ) / (M : ℝ) ^ 4)
        = ∑' d : Fin 4 → CanonicalParts,
            (Real.Gamma (5 / 4 : ℝ) ^ 4 * coefficientWeight d *
              normalizedQuarticLocalDensity M a d) / (M : ℝ) :=
          tsum_congr hterm
    _ = (∑' d : Fin 4 → CanonicalParts,
          Real.Gamma (5 / 4 : ℝ) ^ 4 * coefficientWeight d *
            normalizedQuarticLocalDensity M a d) / (M : ℝ) := by
          simpa only [div_eq_mul_inv] using
            (hsum.tsum_mul_right (M : ℝ)⁻¹)

/-- Final abstract parameter-order theorem. The only remaining arithmetic
hypothesis is that, after `T`, `B`, and `E` have been chosen, a progression
exists with the separate pointwise local estimates (15), (20), (21), and
(8). The regular logarithmic weight is summable by the coefficient
majorant above. -/
theorem exists_quartic_firstMoment_lt_one_eighth
    (regular : (Fin 4 → CanonicalParts) → Prop)
    (rate : (Fin 4 → CanonicalParts) → ℝ)
    (Creg Cuniv : ℝ) (hCreg : 0 ≤ Creg) (hCuniv : 0 ≤ Cuniv)
    (hrate : ∀ d, 0 < rate d)
    (E₀ : Finset CanonicalParts)
    (hbuild : ∀ (T B : ℕ) (E : Finset CanonicalParts),
      0 < B → E₀ ⊆ E →
        Nonempty (QuarticSieveProgression regular rate Creg Cuniv T B E)) :
    ∃ M a : ℕ, ∃ hM : 0 < M,
      a < M ∧
      (letI : NeZero M := ⟨Nat.ne_of_gt hM⟩
       (∑' d : Fin 4 → CanonicalParts,
         fixedPartVolume (fun i => (d i).val) *
           (localCount (fun i => (d i).val) M a : ℝ) / (M : ℝ) ^ 4) <
         1 / (8 * (M : ℝ))) := by
  classical
  have hwsum := summable_regularSieveWeight regular Creg hCreg
  let V : ℝ := Real.Gamma (5 / 4 : ℝ) ^ 4
  let K : ℕ → ℝ := fun T => V * Cuniv * Real.exp ((T : ℝ) + 1)
  have hK : ∀ T, 0 ≤ K T := by
    intro T
    dsimp [K, V]
    positivity
  obtain ⟨T, B, E, hT, hBpos, hB, hEsub, hE⟩ :=
    exists_ordered_coefficient_cutoffs
      (regularSieveWeight regular Creg) rate hwsum
      (regularSieveWeight_nonneg regular Creg hCreg) hrate
      (1 / 40 : ℝ) (by norm_num) (by norm_num)
      K hK E₀ (1 / 32 : ℝ) (by norm_num)
  obtain ⟨S⟩ := hbuild T B E hBpos hEsub
  have hB' : (Real.Gamma (5 / 4 : ℝ) ^ 4 * Cuniv *
      Real.exp ((T : ℝ) + 1)) * Real.log (2 * (B : ℝ)) ^ (30 : ℕ) *
        (∑' d : Fin 4 → CanonicalParts,
          if ∃ p ∈ (coefficientProduct d).primeFactors, B < p then
            coefficientOmegaWeight d else 0) < 1 / 32 := by
    simpa only [K, V] using hB
  have hE' : (Real.Gamma (5 / 4 : ℝ) ^ 4 * Cuniv *
      Real.exp ((T : ℝ) + 1)) * Real.log (2 * (B : ℝ)) ^ (30 : ℕ) *
        (∑' d : Fin 4 → CanonicalParts,
          if ∀ i, d i ∈ E then 0 else coefficientOmegaWeight d) < 1 / 32 := by
    simpa only [K, V] using hE
  obtain ⟨hsum, hglob⟩ := S.global_bound hCreg hCuniv hBpos hrate
    hwsum hT hB' hE'
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

end Erdos940.Quartic
