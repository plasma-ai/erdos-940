module

public import Erdos940.Cubic.Modulus
public import Erdos940.Cubic.Sieve
public import Erdos940.Cubic.LocalUniform
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Products of local cubic densities

The finite product estimates in Section 5 of Beyer–de Ryke. The good primes
and noncube progression are supplied by the preceding modules. All products
here are finite; the estimates do not invoke Chebotarev or an infinite Euler
product.
-/

@[expose] public section

namespace Erdos940

open Finset

/-- The local density factor at a prime. -/
noncomputable def localDensityFactor (q : ℕ) (d : Fin 3 → ℕ) (a : ℕ) : ℝ :=
  (localCountAtModulus d q a : ℝ) / (q : ℝ) ^ 2

theorem localDensityFactor_nonneg (q : ℕ) (d : Fin 3 → ℕ) (a : ℕ) :
    0 ≤ localDensityFactor q d a := by
  unfold localDensityFactor
  positivity

/-- Each good prime saves at least `2/q` of the trivial local density for
coefficient triples drawn from `D`. -/
theorem core_localDensityFactor_le {D : Finset ℕ} {q : ℕ}
    (hq : GoodPrime D q) (d : Fin 3 → ℕ) (hd : ∀ i, d i ∈ D)
    (a : ℕ) (ha : IsNoncubeMod q (a : ZMod q)) :
    localDensityFactor q d a ≤ 1 - 2 / (q : ℝ) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq.1.pos
  have hcount : localCountAtModulus d q a + 2 * q ≤ q * q := by
    rw [localCountAtModulus_eq hq.1.ne_zero]
    exact goodPrime_localCount_bound hq d hd a ha
  have hcountReal : (localCountAtModulus d q a : ℝ) + 2 * (q : ℝ) ≤
      (q : ℝ) ^ 2 := by
    simpa only [pow_two] using (by exact_mod_cast hcount :
      (localCountAtModulus d q a : ℝ) + 2 * (q : ℝ) ≤
        (q : ℝ) * (q : ℝ))
  unfold localDensityFactor
  apply (div_le_iff₀ (pow_pos hqpos 2)).mpr
  have hform : (1 - 2 / (q : ℝ)) * (q : ℝ) ^ 2 =
      (q : ℝ) ^ 2 - 2 * (q : ℝ) := by
    field_simp
  rw [hform]
  linarith

/-- The finite product over good primes satisfies the exponential saving in
equation (13). -/
theorem core_localDensity_product_le_exp {D Q : Finset ℕ}
    (hQ : ∀ q ∈ Q, GoodPrime D q)
    (a : ℕ) (ha : ∀ q ∈ Q, IsNoncubeMod q (a : ZMod q))
    (d : Fin 3 → ℕ) (hd : ∀ i, d i ∈ D) :
    (∏ q ∈ Q, localDensityFactor q d a) ≤
      Real.exp (-2 * ∑ q ∈ Q, (1 : ℝ) / (q : ℝ)) := by
  have hfactor (q : ℕ) (hq : q ∈ Q) :
      localDensityFactor q d a ≤ Real.exp (-2 * ((1 : ℝ) / q)) := by
    have hfirst := core_localDensityFactor_le (hQ q hq) d hd a (ha q hq)
    have hsecond : (1 : ℝ) - 2 / q ≤ Real.exp (-2 * ((1 : ℝ) / q)) := by
      simpa [sub_eq_add_neg, div_eq_mul_inv, mul_assoc, add_comm] using
        (Real.add_one_le_exp (-2 * ((1 : ℝ) / q)))
    exact hfirst.trans hsecond
  calc
    (∏ q ∈ Q, localDensityFactor q d a) ≤
        ∏ q ∈ Q, Real.exp (-2 * ((1 : ℝ) / q)) :=
      Finset.prod_le_prod₀ (fun q _ => localDensityFactor_nonneg q d a) hfactor
    _ = Real.exp (-2 * ∑ q ∈ Q, (1 : ℝ) / (q : ℝ)) := by
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.mul_sum]

/-- Normalize the Chinese-remainder local count by `M³`. The product of
prime-local density factors carries two powers of each prime, leaving one
additional factor `M` in the denominator. -/
theorem localCount_div_cube_eq_localDensity_product_div
    {D Q : Finset ℕ} (hQ : ∀ q ∈ Q, GoodPrime D q)
    (d : Fin 3 → ℕ) (a : ℕ) :
    ((@localCount d (goodModulus Q) a ⟨(goodModulus_pos hQ).ne'⟩ : ℝ) /
        (goodModulus Q : ℝ) ^ 3) =
      (∏ q ∈ Q, localDensityFactor q d a) / (goodModulus Q : ℝ) := by
  have hM : (goodModulus Q : ℝ) = ∏ q ∈ Q, (q : ℝ) := by
    simp [goodModulus]
  have hcount :
      (@localCount d (goodModulus Q) a ⟨(goodModulus_pos hQ).ne'⟩ : ℝ) =
        ∏ q ∈ Q, (localCountAtModulus d q a : ℝ) := by
    exact_mod_cast localCount_goodModulus_eq_prod hQ d a
  have hfactors :
      (∏ q ∈ Q, localDensityFactor q d a) =
        (@localCount d (goodModulus Q) a ⟨(goodModulus_pos hQ).ne'⟩ : ℝ) /
          (goodModulus Q : ℝ) ^ 2 := by
    simp_rw [localDensityFactor]
    rw [Finset.prod_div_distrib, Finset.prod_pow, ← hcount, hM]
  rw [hfactors]
  have hMne : (goodModulus Q : ℝ) ≠ 0 := by
    exact_mod_cast (goodModulus_pos hQ).ne'
  field_simp

/-- How many coefficients vanish modulo `q`. -/
def zeroCoeffCount (q : ℕ) (d : Fin 3 → ℕ) : ℕ :=
  ∑ i : Fin 3, if q ∣ d i then 1 else 0

private theorem noncube_ne_zero {q : ℕ} {a : ℕ}
    (ha : IsNoncubeMod q (a : ZMod q)) : (a : ZMod q) ≠ 0 := by
  intro hzero
  apply ha
  exact ⟨0, by simpa using hzero.symm⟩

/-- At a good prime, a nonvanishing coefficient triple has density at most
`1 + 8/q`. The estimate is uniform in the coefficients. -/
theorem localDensityFactor_le_of_nonzero_coefficients
    {D : Finset ℕ} {q : ℕ} (hq : GoodPrime D q)
    (d : Fin 3 → ℕ) (hd : ∀ i, ¬ q ∣ d i)
    (a : ℕ) (ha : IsNoncubeMod q (a : ZMod q)) :
    localDensityFactor q d a ≤ 1 + 8 / (q : ℝ) := by
  letI : Fact q.Prime := ⟨hq.1⟩
  have hcoeff : ∀ i, (d i : ZMod q) ≠ 0 := by
    intro i
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact hd i
  have hcount : localCountAtModulus d q a ≤ q * q + 8 * q := by
    rw [localCountAtModulus_eq hq.1.ne_zero,
      localCount_eq_localCubicCount_at_prime q d a]
    exact (localCubicCount_nonzero_coefficients_bound_via_gauss q hq.2.1
      (a : ZMod q) (noncube_ne_zero ha) (fun i => (d i : ZMod q)) hcoeff).1
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq.1.pos
  have hcountReal : (localCountAtModulus d q a : ℝ) ≤
      (q : ℝ) ^ 2 + 8 * q := by
    simpa only [pow_two] using (by exact_mod_cast hcount :
      (localCountAtModulus d q a : ℝ) ≤ (q : ℝ) * q + 8 * q)
  unfold localDensityFactor
  apply (div_le_iff₀ (pow_pos hqpos 2)).mpr
  have hform : (1 + 8 / (q : ℝ)) * (q : ℝ) ^ 2 =
      (q : ℝ) ^ 2 + 8 * q := by field_simp
  rw [hform]
  exact hcountReal

/-- Even when coefficients vanish, a nonzero target has at most three
solutions in one variable for each choice of the other two. -/
theorem localDensityFactor_le_three
    {D : Finset ℕ} {q : ℕ} (hq : GoodPrime D q)
    (d : Fin 3 → ℕ) (a : ℕ) (ha : IsNoncubeMod q (a : ZMod q)) :
    localDensityFactor q d a ≤ 3 := by
  letI : Fact q.Prime := ⟨hq.1⟩
  have hcount : localCountAtModulus d q a ≤ 3 * q * q := by
    rw [localCountAtModulus_eq hq.1.ne_zero,
      localCount_eq_localCubicCount_at_prime q d a]
    simpa [ZMod.card q] using
      localCubicCount_le_three_sq (ZMod q) (a : ZMod q)
        (noncube_ne_zero ha) (fun i => (d i : ZMod q))
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq.1.pos
  have hcountReal : (localCountAtModulus d q a : ℝ) ≤
      3 * (q : ℝ) ^ 2 := by
    simpa only [pow_two, mul_assoc] using (by exact_mod_cast hcount :
      (localCountAtModulus d q a : ℝ) ≤ 3 * (q : ℝ) * q)
  unfold localDensityFactor
  apply (div_le_iff₀ (pow_pos hqpos 2)).mpr
  nlinarith

/-- A vanishing coefficient is charged one factor of three. -/
theorem localDensityFactor_le_uniform
    {D : Finset ℕ} {q : ℕ} (hq : GoodPrime D q)
    (d : Fin 3 → ℕ) (a : ℕ) (ha : IsNoncubeMod q (a : ZMod q)) :
    localDensityFactor q d a ≤
      (1 + 8 / (q : ℝ)) * (3 : ℝ) ^ zeroCoeffCount q d := by
  by_cases h : ∃ i, q ∣ d i
  · obtain ⟨i, hi⟩ := h
    have hcount : 1 ≤ zeroCoeffCount q d := by
      unfold zeroCoeffCount
      calc
        1 = (if q ∣ d i then 1 else 0) := by simp [hi]
        _ ≤ ∑ j : Fin 3, if q ∣ d j then 1 else 0 := by
          exact Finset.single_le_sum (s := Finset.univ)
            (f := fun j : Fin 3 => if q ∣ d j then 1 else 0)
            (by intro j hj; split_ifs <;> omega) (Finset.mem_univ i)
    have hpow : (3 : ℝ) ≤ 3 ^ zeroCoeffCount q d := by
      calc
        (3 : ℝ) = 3 ^ (1 : ℕ) := by simp
        _ ≤ 3 ^ zeroCoeffCount q d :=
          pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hcount
    have hqpos : (0 : ℝ) < q := by exact_mod_cast hq.1.pos
    have hnonneg : 0 ≤ 8 / (q : ℝ) := le_of_lt (div_pos (by norm_num) hqpos)
    calc
      localDensityFactor q d a ≤ 3 := localDensityFactor_le_three hq d a ha
      _ ≤ (1 + 8 / (q : ℝ)) * (3 : ℝ) ^ zeroCoeffCount q d := by
        nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) (zeroCoeffCount q d)]
  · have hd : ∀ i, ¬ q ∣ d i := by simpa using h
    have hzero : zeroCoeffCount q d = 0 := by
      simp [zeroCoeffCount, hd]
    simpa [hzero] using localDensityFactor_le_of_nonzero_coefficients hq d hd a ha

/-- Across distinct good primes, each vanishing coefficient is charged to a
distinct prime factor of that coefficient. -/
theorem sum_zeroCoeffCount_le_primeFactors
    {D Q : Finset ℕ} (hQ : ∀ q ∈ Q, GoodPrime D q)
    (d : Fin 3 → ℕ) (hd : ∀ i, 0 < d i) :
    (∑ q ∈ Q, zeroCoeffCount q d) ≤
      ∑ i : Fin 3, (d i).primeFactors.card := by
  have hone (i : Fin 3) :
      (∑ q ∈ Q, if q ∣ d i then 1 else 0) ≤ (d i).primeFactors.card := by
    rw [Finset.sum_boole]
    apply Finset.card_le_card
    intro q hq
    have hqQ : q ∈ Q := (Finset.mem_filter.mp hq).1
    have hdiv : q ∣ d i := (Finset.mem_filter.mp hq).2
    exact Nat.mem_primeFactors.mpr ⟨(hQ q hqQ).1, hdiv, (hd i).ne'⟩
  calc
    (∑ q ∈ Q, zeroCoeffCount q d) =
        ∑ i : Fin 3, ∑ q ∈ Q, if q ∣ d i then 1 else 0 := by
          simp_rw [zeroCoeffCount]
          rw [Finset.sum_comm]
    _ ≤ ∑ i : Fin 3, (d i).primeFactors.card :=
      Finset.sum_le_sum (fun i _ => hone i)

/-- The finite middle-triple local product estimate from Section 5. This
version applies to every positive coefficient triple; membership in
`E³ \ D³` is used only when summing over triples later. -/
theorem middle_localDensity_product_le_exp
    {D Q : Finset ℕ} (hQ : ∀ q ∈ Q, GoodPrime D q)
    (a : ℕ) (ha : ∀ q ∈ Q, IsNoncubeMod q (a : ZMod q))
    (d : Fin 3 → ℕ) (hd : ∀ i, 0 < d i) :
    (∏ q ∈ Q, localDensityFactor q d a) ≤
      Real.exp (8 * ∑ q ∈ Q, (1 : ℝ) / (q : ℝ)) *
        (3 : ℝ) ^ (∑ i : Fin 3, (d i).primeFactors.card) := by
  have hexp :
      (∏ q ∈ Q, (1 + 8 / (q : ℝ))) ≤
        Real.exp (8 * ∑ q ∈ Q, (1 : ℝ) / (q : ℝ)) := by
    have hfactor (q : ℕ) (hq : q ∈ Q) :
        1 + 8 / (q : ℝ) ≤ Real.exp (8 * ((1 : ℝ) / q)) := by
      simpa [div_eq_mul_inv, mul_assoc, add_comm] using
        (Real.add_one_le_exp (8 * ((1 : ℝ) / q)))
    calc
      (∏ q ∈ Q, (1 + 8 / (q : ℝ))) ≤
          ∏ q ∈ Q, Real.exp (8 * ((1 : ℝ) / q)) := by
            apply Finset.prod_le_prod₀
            · intro q hq
              have hqpos : (0 : ℝ) < q := by exact_mod_cast (hQ q hq).1.pos
              positivity
            · exact hfactor
      _ = Real.exp (8 * ∑ q ∈ Q, (1 : ℝ) / (q : ℝ)) := by
        rw [← Real.exp_sum]
        congr 1
        rw [Finset.mul_sum]
  have hzeros := sum_zeroCoeffCount_le_primeFactors hQ d hd
  have hpowers :
      (3 : ℝ) ^ (∑ q ∈ Q, zeroCoeffCount q d) ≤
        (3 : ℝ) ^ (∑ i : Fin 3, (d i).primeFactors.card) :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hzeros
  calc
    (∏ q ∈ Q, localDensityFactor q d a) ≤
        ∏ q ∈ Q, ((1 + 8 / (q : ℝ)) *
          (3 : ℝ) ^ zeroCoeffCount q d) :=
      Finset.prod_le_prod₀
        (fun q _ => localDensityFactor_nonneg q d a)
        (fun q hq => localDensityFactor_le_uniform (hQ q hq) d a (ha q hq))
    _ = (∏ q ∈ Q, (1 + 8 / (q : ℝ))) *
          (3 : ℝ) ^ (∑ q ∈ Q, zeroCoeffCount q d) := by
        rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    _ ≤ Real.exp (8 * ∑ q ∈ Q, (1 : ℝ) / (q : ℝ)) *
          (3 : ℝ) ^ (∑ q ∈ Q, zeroCoeffCount q d) :=
      mul_le_mul_of_nonneg_right hexp (pow_nonneg (by norm_num) _)
    _ ≤ Real.exp (8 * ∑ q ∈ Q, (1 : ℝ) / (q : ℝ)) *
          (3 : ℝ) ^ (∑ i : Fin 3, (d i).primeFactors.card) :=
      mul_le_mul_of_nonneg_left hpowers (Real.exp_pos _).le

end Erdos940
