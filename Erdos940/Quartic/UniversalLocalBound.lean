import Erdos940.Quartic.LocalFactorAssembly
import Erdos940.Quartic.SieveAssembly

/-!
# Universal finite-product estimate for quartic local densities

This separates the elementary accounting for coefficient primes from the
prime-harmonic bound. A coefficient prime costs at most four; every other
odd prime costs at most `exp (21 / p)`.
-/

namespace Erdos940.Quartic

open Finset

/-- A finite product with exceptional factors and variable good-prime costs. -/
theorem quartic_finite_product_le_bad_four_mul_exp_cost
    (Q : Finset ℕ) (f : ℕ → ℝ) (bad : ℕ → Prop) [DecidablePred bad]
    (cost : ℕ → ℝ)
    (hnonneg : ∀ p ∈ Q, 0 ≤ f p)
    (hcost : ∀ p ∈ Q, 0 ≤ cost p)
    (hbad : ∀ p ∈ Q, bad p → f p ≤ 4)
    (hgood : ∀ p ∈ Q, ¬bad p → f p ≤ Real.exp (cost p)) :
    (∏ p ∈ Q, f p) ≤
      (4 : ℝ) ^ (Q.filter bad).card *
        Real.exp (∑ p ∈ Q, cost p) := by
  classical
  let g : ℕ → ℝ := fun p => if bad p then 4 else 1
  have hpoint (p : ℕ) (hp : p ∈ Q) :
      f p ≤ g p * Real.exp (cost p) := by
    by_cases hb : bad p
    · have he : 1 ≤ Real.exp (cost p) := Real.one_le_exp (hcost p hp)
      have := hbad p hp hb
      simp only [g, if_pos hb]
      nlinarith
    · simpa [g, hb] using hgood p hp hb
  calc
    (∏ p ∈ Q, f p) ≤ ∏ p ∈ Q, g p * Real.exp (cost p) :=
      Finset.prod_le_prod₀ hnonneg hpoint
    _ = (∏ p ∈ Q, g p) * (∏ p ∈ Q, Real.exp (cost p)) := by
      rw [Finset.prod_mul_distrib]
    _ = (4 : ℝ) ^ (Q.filter bad).card *
        Real.exp (∑ p ∈ Q, cost p) := by
      simp [g, Finset.prod_ite, Finset.prod_const, Real.exp_sum]

/-- A finite product with finitely many exceptional factors. -/
theorem quartic_finite_product_le_bad_four_mul_exp
    (Q : Finset ℕ) (f : ℕ → ℝ) (bad : ℕ → Prop) [DecidablePred bad]
    (hnonneg : ∀ p ∈ Q, 0 ≤ f p)
    (hbad : ∀ p ∈ Q, bad p → f p ≤ 4)
    (hgood : ∀ p ∈ Q, ¬bad p → f p ≤ Real.exp (21 / (p : ℝ))) :
    (∏ p ∈ Q, f p) ≤
      (4 : ℝ) ^ (Q.filter bad).card *
        Real.exp (21 * ∑ p ∈ Q, (p : ℝ)⁻¹) := by
  classical
  let g : ℕ → ℝ := fun p => if bad p then 4 else 1
  have hpoint (p : ℕ) (hp : p ∈ Q) :
      f p ≤ g p * Real.exp (21 / (p : ℝ)) := by
    by_cases hb : bad p
    · have he : 1 ≤ Real.exp (21 / (p : ℝ)) := by
        apply Real.one_le_exp
        positivity
      have := hbad p hp hb
      simp only [g, if_pos hb]
      nlinarith
    · have := hgood p hp hb
      simpa [g, hb] using this
  have hg (p : ℕ) (hp : p ∈ Q) : 0 ≤ g p := by
    simp only [g]
    split_ifs <;> norm_num
  calc
    (∏ p ∈ Q, f p) ≤ ∏ p ∈ Q, g p * Real.exp (21 / (p : ℝ)) :=
      Finset.prod_le_prod₀ hnonneg hpoint
    _ = (∏ p ∈ Q, g p) * (∏ p ∈ Q, Real.exp (21 / (p : ℝ))) := by
      rw [Finset.prod_mul_distrib]
    _ = (4 : ℝ) ^ (Q.filter bad).card *
        Real.exp (21 * ∑ p ∈ Q, (p : ℝ)⁻¹) := by
      have hgprod : (∏ p ∈ Q, g p) = (4 : ℝ) ^ (Q.filter bad).card := by
        simp [g, Finset.prod_ite, Finset.prod_const]
      rw [hgprod, ← Real.exp_sum]
      congr 1
      rw [Finset.mul_sum]
      simp only [div_eq_mul_inv]

/-- The coefficient primes charged at cost four are among the prime factors
of the coefficient product. -/
theorem quartic_coefficient_prime_filter_card_le
    (Q : Finset ℕ) (d : Fin 4 → CanonicalParts)
    (hprime : ∀ p ∈ Q, p.Prime) :
    (Q.filter (fun p => ∃ i, p ∣ (d i).val)).card ≤
      (coefficientProduct d).primeFactors.card := by
  classical
  apply Finset.card_le_card
  intro p hp
  obtain ⟨hpQ, i, hpi⟩ := Finset.mem_filter.mp hp
  have hDpos : 0 < coefficientProduct d := by
    unfold coefficientProduct
    exact Finset.prod_pos (fun i _ => CanonicalPart.pos (d i).property)
  apply (hprime p hpQ).mem_primeFactors _ hDpos.ne'
  exact hpi.trans (by
    unfold coefficientProduct
    exact Finset.dvd_prod_of_mem (fun i : Fin 4 => (d i).val) (Finset.mem_univ i))

/-- The variable-cost product bound with the coefficient-prime count absorbed
into `4^ω(D)`. -/
theorem quartic_local_product_le_coefficient_weight_exp_cost
    (Q : Finset ℕ) (d : Fin 4 → CanonicalParts)
    (f : ℕ → ℝ) (cost : ℕ → ℝ) (H : ℝ)
    (hprime : ∀ p ∈ Q, p.Prime)
    (hnonneg : ∀ p ∈ Q, 0 ≤ f p)
    (hcost : ∀ p ∈ Q, 0 ≤ cost p)
    (hbad : ∀ p ∈ Q, (∃ i, p ∣ (d i).val) → f p ≤ 4)
    (hgood : ∀ p ∈ Q, (∀ i, ¬p ∣ (d i).val) →
      f p ≤ Real.exp (cost p))
    (hbudget : (∑ p ∈ Q, cost p) ≤ H) :
    (∏ p ∈ Q, f p) ≤
      (4 : ℝ) ^ (coefficientProduct d).primeFactors.card * Real.exp H := by
  classical
  let bad : ℕ → Prop := fun p => ∃ i, p ∣ (d i).val
  have hgood' (p : ℕ) (hp : p ∈ Q) (hb : ¬bad p) :
      f p ≤ Real.exp (cost p) :=
    hgood p hp (by simpa [bad, not_exists] using hb)
  have hprod := quartic_finite_product_le_bad_four_mul_exp_cost
    Q f bad cost hnonneg hcost hbad hgood'
  have hcard := quartic_coefficient_prime_filter_card_le Q d hprime
  have hfour : (4 : ℝ) ^ (Q.filter bad).card ≤
      (4 : ℝ) ^ (coefficientProduct d).primeFactors.card :=
    pow_le_pow_right₀ (by norm_num) (by simpa [bad] using hcard)
  exact hprod.trans <| mul_le_mul hfour (Real.exp_le_exp.mpr hbudget)
    (Real.exp_pos _).le (by positivity)

/-- A ready-to-use universal selected-prime factor bound. The only
arithmetic hypotheses are the local factor estimates and a reciprocal-prime
budget; there is no dependence on the number of selected primes. -/
theorem quartic_local_product_le_coefficient_weight_exp
    (Q : Finset ℕ) (d : Fin 4 → CanonicalParts) (f : ℕ → ℝ) (H : ℝ)
    (hprime : ∀ p ∈ Q, p.Prime)
    (hnonneg : ∀ p ∈ Q, 0 ≤ f p)
    (hbad : ∀ p ∈ Q, (∃ i, p ∣ (d i).val) → f p ≤ 4)
    (hgood : ∀ p ∈ Q, (∀ i, ¬p ∣ (d i).val) →
      f p ≤ Real.exp (21 / (p : ℝ)))
    (hbudget : (∑ p ∈ Q, (p : ℝ)⁻¹) ≤ H) :
    (∏ p ∈ Q, f p) ≤
      (4 : ℝ) ^ (coefficientProduct d).primeFactors.card *
        Real.exp (21 * H) := by
  classical
  let bad : ℕ → Prop := fun p => ∃ i, p ∣ (d i).val
  have hgood' (p : ℕ) (hp : p ∈ Q) (hb : ¬bad p) :
      f p ≤ Real.exp (21 / (p : ℝ)) :=
    hgood p hp (by simpa [bad, not_exists] using hb)
  have hprod := quartic_finite_product_le_bad_four_mul_exp Q f bad
    hnonneg hbad hgood'
  have hcard := quartic_coefficient_prime_filter_card_le Q d hprime
  have hfour : (4 : ℝ) ^ (Q.filter bad).card ≤
      (4 : ℝ) ^ (coefficientProduct d).primeFactors.card :=
    pow_le_pow_right₀ (by norm_num) (by simpa [bad] using hcard)
  have hsum : 21 * (∑ p ∈ Q, (p : ℝ)⁻¹) ≤ 21 * H := by
    nlinarith
  exact hprod.trans <| mul_le_mul hfour (Real.exp_le_exp.mpr hsum)
    (Real.exp_pos _).le (by positivity)

end Erdos940.Quartic
