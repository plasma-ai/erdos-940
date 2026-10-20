import Erdos940.Quartic.LocalQuartic
import Erdos940.Quartic.LocalCRT
import Erdos940.Quartic.EulerProductInequality

/-!
# Assembly of finite quartic local factors

This module connects the valuation-one calculations to the normalized CRT
product. The good-prime trace remains an explicit input; no analytic estimate
of its Euler product is used here.
-/

namespace Erdos940.Quartic

open Finset

theorem localCountAtModulus_eq_quartic_nat_card (d : Fin 4 → ℕ)
    (M a : ℕ) (hM : M ≠ 0) :
    localCountAtModulus d M a =
      Nat.card {x : Fin 4 → ZMod M //
        (∑ i, (d i : ZMod M) * x i ^ 4) = (a : ZMod M)} := by
  haveI : NeZero M := ⟨hM⟩
  simp [localCountAtModulus, hM, localCount, quarticFormMod,
    Nat.card_eq_fintype_card]
  rfl

/-- Canonical coefficient valuations, expressed modulo `p²`, have no
valuation-one coefficient. -/
theorem quartic_coefficient_reduction_zero_implies_square_zero
    (p : ℕ) (_hp : p.Prime) (d : Fin 4 → ℕ)
    (hd : ∀ i, p ∣ d i → p ^ 2 ∣ d i) (i : Fin 4) :
    (ZMod.cast (d i : ZMod (p ^ 2)) : ZMod p) = 0 →
      (d i : ZMod (p ^ 2)) = 0 := by
  intro hi
  rw [ZMod.cast_natCast (show p ∣ p ^ 2 by simp)] at hi
  exact (ZMod.natCast_eq_zero_iff (d i) (p ^ 2)).mpr
    (hd i ((ZMod.natCast_eq_zero_iff (d i) p).mp hi))

/-- At a coefficient prime, equation (14) bounds the normalized `p²` factor
by four. -/
theorem localDensityFactor_prime_square_le_four (p : ℕ) (hp : p.Prime)
    [Fact p.Prime] (d : Fin 4 → ℕ)
    (hd : ∀ i, p ∣ d i → p ^ 2 ∣ d i)
    (hfour : (4 : ZMod p) ≠ 0) :
    localDensityFactor (p ^ 2) d p ≤ 4 := by
  have hM : p ^ 2 ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hcount : localCountAtModulus d (p ^ 2) p ≤ 4 * p ^ 6 := by
    rw [localCountAtModulus_eq_quartic_nat_card d (p ^ 2) p hM]
    exact zmod_prime_square_quartic_count_le_four_cube_square p hp
      (fun i => (d i : ZMod (p ^ 2)))
      (quartic_coefficient_reduction_zero_implies_square_zero p hp d hd) hfour
  have hpR : (0 : ℝ) < (p : ℝ) ^ 6 := by
    have : (0 : ℝ) < p := by exact_mod_cast hp.pos
    positivity
  have hden : ((p ^ 2 : ℕ) : ℝ) ^ 3 = (p : ℝ) ^ 6 := by
    push_cast
    ring
  change (localCountAtModulus d (p ^ 2) p : ℝ) /
    ((p ^ 2 : ℕ) : ℝ) ^ 3 ≤ 4
  rw [hden]
  apply (div_le_iff₀ hpR).2
  exact_mod_cast hcount

/-- Equation (13) for the `localDensityFactor` interface used by the CRT
product. -/
theorem localDensityFactor_prime_square_eq_prime_zero_density_sub (p : ℕ)
    (hp : p.Prime) [Fact p.Prime] (d : Fin 4 → ℕ)
    (hunit : ∀ i, (d i : ZMod p) ≠ 0)
    (hfour : (4 : ZMod p) ≠ 0) :
    localDensityFactor (p ^ 2) d p =
      (localQuarticCount (ZMod p) 0 (fun i => (d i : ZMod p)) : ℝ) /
        (p : ℝ) ^ 3 - 1 / (p : ℝ) ^ 3 := by
  have hM : p ^ 2 ≠ 0 := pow_ne_zero _ hp.ne_zero
  have ha (i : Fin 4) :
      (ZMod.cast (d i : ZMod (p ^ 2)) : ZMod p) ≠ 0 := by
    simpa only [ZMod.cast_natCast (show p ∣ p ^ 2 by simp)] using hunit i
  have hrat := zmod_prime_square_quartic_density_eq_prime_zero_density_sub
    p hp (fun i => (d i : ZMod (p ^ 2))) ha hfour
  have hreal :
      (Nat.card {x : Fin 4 → ZMod (p ^ 2) //
        (∑ j, (d j : ZMod (p ^ 2)) * x j ^ 4) =
          (p : ZMod (p ^ 2))} : ℝ) / (p : ℝ) ^ 6 =
        (localQuarticCount (ZMod p) 0 (fun i => (d i : ZMod p)) : ℝ) /
          (p : ℝ) ^ 3 - 1 / (p : ℝ) ^ 3 := by
    have hreal0 := congrArg (fun z : ℚ => (z : ℝ)) hrat
    push_cast at hreal0
    simpa only [ZMod.cast_natCast (show p ∣ p ^ 2 by simp)] using hreal0
  have hden : ((p ^ 2 : ℕ) : ℝ) ^ 3 = (p : ℝ) ^ 6 := by
    push_cast
    ring
  unfold localDensityFactor
  rw [localCountAtModulus_eq_quartic_nat_card d (p ^ 2) p hM, hden]
  exact hreal

/-- Insert any independently established prime-field trace `A` into the
valuation-one local factor. This is the good-prime factor of (13) and (10). -/
theorem localDensityFactor_good_prime_formula (p : ℕ) (hp : p.Prime)
    [Fact p.Prime] (d : Fin 4 → ℕ) (A : ℝ)
    (hunit : ∀ i, (d i : ZMod p) ≠ 0)
    (hfour : (4 : ZMod p) ≠ 0)
    (htrace :
      (localQuarticCount (ZMod p) 0 (fun i => (d i : ZMod p)) : ℝ) /
        (p : ℝ) ^ 3 =
          1 + A * ((p : ℝ)⁻¹ - ((p : ℝ) ^ 2)⁻¹)) :
    localDensityFactor (p ^ 2) d p =
      1 + A * ((p : ℝ)⁻¹ - ((p : ℝ) ^ 2)⁻¹) - ((p : ℝ) ^ 3)⁻¹ := by
  rw [localDensityFactor_prime_square_eq_prime_zero_density_sub p hp d hunit hfour,
    htrace, one_div]

/-- The trivial four-variable bound, used for the modulus-16 factor. -/
theorem localCountAtModulus_le_fourth (d : Fin 4 → ℕ) (M a : ℕ)
    (hM : M ≠ 0) : localCountAtModulus d M a ≤ M ^ 4 := by
  classical
  haveI : NeZero M := ⟨hM⟩
  rw [localCountAtModulus_eq_quartic_nat_card d M a hM,
    Nat.card_eq_fintype_card]
  calc
    Fintype.card {x : Fin 4 → ZMod M //
        (∑ i, (d i : ZMod M) * x i ^ 4) = (a : ZMod M)} ≤
      Fintype.card (Fin 4 → ZMod M) := Fintype.card_subtype_le _
    _ = M ^ 4 := by simp

/-- In particular, the density at modulus 16 is at most 16, including the
target 8 used in the obstruction modulus. -/
theorem localDensityFactor_sixteen_le_sixteen (d : Fin 4 → ℕ) (a : ℕ) :
    localDensityFactor 16 d a ≤ 16 := by
  have hcount := localCountAtModulus_le_fourth d 16 a (by decide)
  change (localCountAtModulus d 16 a : ℝ) / (16 : ℝ) ^ 3 ≤ 16
  apply (div_le_iff₀ (by norm_num)).2
  norm_num
  exact_mod_cast hcount

/-- A local factor depends only on the target residue class. -/
theorem localDensityFactor_congr_target (M : ℕ) (hM : M ≠ 0)
    (d : Fin 4 → ℕ) (a b : ℕ)
    (hab : (a : ZMod M) = (b : ZMod M)) :
    localDensityFactor M d a = localDensityFactor M d b := by
  haveI : NeZero M := ⟨hM⟩
  unfold localDensityFactor
  congr 1
  rw [localCountAtModulus_eq_quartic_nat_card d M a hM,
    localCountAtModulus_eq_quartic_nat_card d M b hM]
  simp only [← hab]

/-- Any pointwise bounds for the local density factors multiply across the
finite CRT modulus. -/
theorem localCount_CRT_le_local_factor_product {Q : Finset ℕ}
    (hQ : ∀ q ∈ Q, 0 < q)
    (hcoprime : ∀ q ∈ Q, ∀ r ∈ Q, q ≠ r → q.Coprime r)
    (d : Fin 4 → ℕ) (a : ℕ) (B : ℕ → ℝ)
    (hB : ∀ q ∈ Q, localDensityFactor q d a ≤ B q) :
    ((@localCount d (quarticModulus Q) a
      ⟨(quarticModulus_pos hQ).ne'⟩ : ℝ) /
      (quarticModulus Q : ℝ) ^ 4) ≤
      (∏ q ∈ Q, B q) / (quarticModulus Q : ℝ) := by
  rw [localCount_div_fourth_eq_localDensity_product_div hQ hcoprime d a]
  have hprod : (∏ q ∈ Q, localDensityFactor q d a) ≤ ∏ q ∈ Q, B q := by
    apply Finset.prod_le_prod₀
    · intro q _
      exact localDensityFactor_nonneg q d a
    · exact hB
  have hM : (0 : ℝ) ≤ (quarticModulus Q : ℝ) := by
    exact_mod_cast (Nat.zero_le (quarticModulus Q))
  exact div_le_div_of_nonneg_right hprod hM

/-- The factorwise upper envelope: modulus 16 costs 16, a coefficient
prime costs 4, and every other prime uses its quartic trace. -/
noncomputable def quarticLocalMajorant (d : Fin 4 → ℕ)
    (r : ℕ → ℕ) (A : ℕ → ℝ) (q : ℕ) : ℝ := by
  classical
  exact if q = 16 then 16
    else if ∃ i : Fin 4, r q ∣ d i then 4
    else 1 + A (r q) *
      (((r q : ℕ) : ℝ)⁻¹ - ((((r q : ℕ) : ℝ) ^ 2)⁻¹)) -
        ((((r q : ℕ) : ℝ) ^ 3)⁻¹)

/-- Finite CRT majorant for the valuation-one local targets. The specified
residue condition says the global target reduces to `p` modulo each selected
`p²`; no analytic Euler-product hypothesis is present. -/
theorem localCount_CRT_le_quartic_local_majorant {Q : Finset ℕ}
    (hQ : ∀ q ∈ Q, 0 < q)
    (hcoprime : ∀ q ∈ Q, ∀ r ∈ Q, q ≠ r → q.Coprime r)
    (d : Fin 4 → ℕ) (a : ℕ) (r : ℕ → ℕ) (A : ℕ → ℝ)
    (hprime : ∀ q ∈ Q, q ≠ 16 → (r q).Prime)
    (hsquare : ∀ q ∈ Q, q ≠ 16 → q = (r q) ^ 2)
    (htarget : ∀ q ∈ Q, q ≠ 16 →
      (a : ZMod q) = (r q : ZMod q))
    (hcanonical : ∀ q ∈ Q, q ≠ 16 →
      ∀ i, r q ∣ d i → (r q) ^ 2 ∣ d i)
    (hfour : ∀ q ∈ Q, q ≠ 16 → (4 : ZMod (r q)) ≠ 0)
    (htrace : ∀ q ∈ Q, q ≠ 16 →
      (∀ i, ¬r q ∣ d i) →
      (Nat.card {y : Fin 4 → ZMod (r q) //
        (∑ i, (d i : ZMod (r q)) * y i ^ 4) = 0} : ℝ) /
        (r q : ℝ) ^ 3 =
        1 + A (r q) * ((r q : ℝ)⁻¹ - ((r q : ℝ) ^ 2)⁻¹)) :
    ((@localCount d (quarticModulus Q) a
      ⟨(quarticModulus_pos hQ).ne'⟩ : ℝ) /
      (quarticModulus Q : ℝ) ^ 4) ≤
      (∏ q ∈ Q, quarticLocalMajorant d r A q) /
        (quarticModulus Q : ℝ) := by
  classical
  apply localCount_CRT_le_local_factor_product hQ hcoprime d a
    (quarticLocalMajorant d r A)
  intro q hq
  by_cases h16 : q = 16
  · subst q
    simpa [quarticLocalMajorant] using localDensityFactor_sixteen_le_sixteen d a
  · let p := r q
    have hp : p.Prime := hprime q hq h16
    letI : Fact p.Prime := ⟨hp⟩
    have hqeq : q = p ^ 2 := hsquare q hq h16
    have hM : p ^ 2 ≠ 0 := pow_ne_zero _ hp.ne_zero
    have hfactor : localDensityFactor q d a = localDensityFactor (p ^ 2) d p := by
      calc
        localDensityFactor q d a = localDensityFactor q d p :=
          localDensityFactor_congr_target q (hQ q hq).ne' d a p
            (htarget q hq h16)
        _ = localDensityFactor (p ^ 2) d p := by rw [hqeq]
    rw [hfactor]
    by_cases hbad : ∃ i : Fin 4, p ∣ d i
    · have hle := localDensityFactor_prime_square_le_four p hp d
        (hcanonical q hq h16) (hfour q hq h16)
      simpa [quarticLocalMajorant, h16, p, hbad] using hle
    · have hunit (i : Fin 4) : (d i : ZMod p) ≠ 0 := by
        intro hi
        exact hbad ⟨i, (ZMod.natCast_eq_zero_iff (d i) p).mp hi⟩
      have hnone (i : Fin 4) : ¬p ∣ d i := by
        intro hi
        exact hbad ⟨i, hi⟩
      have htr :
          (localQuarticCount (ZMod p) 0
              (fun i => (d i : ZMod p)) : ℝ) / (p : ℝ) ^ 3 =
            1 + A p * ((p : ℝ)⁻¹ - ((p : ℝ) ^ 2)⁻¹) := by
        simpa only [localQuarticCount, Nat.card_eq_fintype_card] using
          htrace q hq h16 hnone
      have heq := localDensityFactor_good_prime_formula p hp d (A p)
        hunit (hfour q hq h16) htr
      simpa [quarticLocalMajorant, h16, p, hbad] using le_of_eq heq

/-- The selected-prime valuation-one factor, after equation (11) identifies
its trace with a quadratic character. -/
noncomputable def quarticSelectedFactor (p : ℕ) (A : ℝ) : ℝ :=
  1 + A * ((p : ℝ)⁻¹ - ((p : ℝ) ^ 2)⁻¹) - ((p : ℝ) ^ 3)⁻¹

/-- For a trace at least `-1`, the second-order correction to the prime
reciprocal is at most one reciprocal square. -/
theorem quarticSelectedFactor_le_exp (p : ℕ) (hp : 0 < p)
    (A : ℝ) (hA : -A ≤ 1) :
    quarticSelectedFactor p A ≤
      Real.exp (A / (p : ℝ) + 1 / (p : ℝ) ^ 2) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hsq : 0 ≤ ((p : ℝ) ^ 2)⁻¹ := by positivity
  have hcube : 0 ≤ ((p : ℝ) ^ 3)⁻¹ := by positivity
  have herror : (-A) * ((p : ℝ) ^ 2)⁻¹ ≤ ((p : ℝ) ^ 2)⁻¹ := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hA hsq
  have hlin : A * ((p : ℝ)⁻¹ - ((p : ℝ) ^ 2)⁻¹) -
      ((p : ℝ) ^ 3)⁻¹ ≤ A / (p : ℝ) + 1 / (p : ℝ) ^ 2 := by
    rw [div_eq_mul_inv, one_div]
    nlinarith [herror, hcube]
  calc
    quarticSelectedFactor p A ≤
        Real.exp (A * ((p : ℝ)⁻¹ - ((p : ℝ) ^ 2)⁻¹) -
          ((p : ℝ) ^ 3)⁻¹) := by
      unfold quarticSelectedFactor
      convert Real.add_one_le_exp
        (A * ((p : ℝ)⁻¹ - ((p : ℝ) ^ 2)⁻¹) - ((p : ℝ) ^ 3)⁻¹) using 1 <;> ring
    _ ≤ Real.exp (A / (p : ℝ) + 1 / (p : ℝ) ^ 2) :=
      Real.exp_le_exp.mpr hlin

/-- The finite selected-prime estimate underlying (20): the selector's
character bias and reciprocal-square budget become exponential decay. -/
theorem quarticSelectedProduct_le_exp (Q : Finset ℕ) (A : ℕ → ℝ)
    (T rate : ℝ)
    (hp : ∀ p ∈ Q, 0 < p)
    (hA : ∀ p ∈ Q, -A p ≤ 1)
    (hfactor : ∀ p ∈ Q, 0 ≤ quarticSelectedFactor p (A p))
    (hbias : (∑ p ∈ Q, A p / (p : ℝ)) ≤ -(T * rate) + 1)
    (hsquare : (∑ p ∈ Q, (1 : ℝ) / (p : ℝ) ^ 2) ≤ 1) :
    (∏ p ∈ Q, quarticSelectedFactor p (A p)) ≤
      Real.exp (-(T * rate) + 2) := by
  calc
    (∏ p ∈ Q, quarticSelectedFactor p (A p)) ≤
        ∏ p ∈ Q, Real.exp (A p / (p : ℝ) + 1 / (p : ℝ) ^ 2) :=
      Finset.prod_le_prod₀ (fun p h => hfactor p h)
        (fun p h => quarticSelectedFactor_le_exp p (hp p h) (A p) (hA p h))
    _ = Real.exp (∑ p ∈ Q,
          (A p / (p : ℝ) + 1 / (p : ℝ) ^ 2)) := by
      rw [Real.exp_sum]
    _ ≤ Real.exp (-(T * rate) + 2) := by
      apply Real.exp_le_exp.mpr
      rw [Finset.sum_add_distrib]
      linarith

/-- Direct `selectedDensity` interface for the sieve assembly: equations
(11) and (13), the selector's biased character sum, and its reciprocal-square
budget imply (20). -/
theorem selectedLocalDensityProduct_le_exp (Q : Finset ℕ)
    (d : Fin 4 → ℕ) (A : ℕ → ℝ) (T rate : ℝ)
    (hprime : ∀ p ∈ Q, p.Prime)
    (hunit : ∀ p ∈ Q, ∀ i, (d i : ZMod p) ≠ 0)
    (hfour : ∀ p ∈ Q, (4 : ZMod p) ≠ 0)
    (htrace : ∀ p ∈ Q,
      (Nat.card {y : Fin 4 → ZMod p //
        (∑ i, (d i : ZMod p) * y i ^ 4) = 0} : ℝ) /
        (p : ℝ) ^ 3 =
        1 + A p * ((p : ℝ)⁻¹ - ((p : ℝ) ^ 2)⁻¹))
    (hA : ∀ p ∈ Q, -A p ≤ 1)
    (hbias : (∑ p ∈ Q, A p / (p : ℝ)) ≤ -(T * rate) + 1)
    (hsquare : (∑ p ∈ Q, (1 : ℝ) / (p : ℝ) ^ 2) ≤ 1) :
    (∏ p ∈ Q, localDensityFactor (p ^ 2) d p) ≤
      Real.exp (-(T * rate) + 2) := by
  classical
  have hfactor (p : ℕ) (hpQ : p ∈ Q) :
      localDensityFactor (p ^ 2) d p = quarticSelectedFactor p (A p) := by
    letI : Fact p.Prime := ⟨hprime p hpQ⟩
    have htr :
        (localQuarticCount (ZMod p) 0
          (fun i => (d i : ZMod p)) : ℝ) / (p : ℝ) ^ 3 =
        1 + A p * ((p : ℝ)⁻¹ - ((p : ℝ) ^ 2)⁻¹) := by
      simpa only [localQuarticCount, Nat.card_eq_fintype_card] using
        htrace p hpQ
    simpa only [quarticSelectedFactor] using
      localDensityFactor_good_prime_formula p (hprime p hpQ) d (A p)
        (hunit p hpQ) (hfour p hpQ) htr
  have hnonneg (p : ℕ) (hpQ : p ∈ Q) :
      0 ≤ quarticSelectedFactor p (A p) := by
    rw [← hfactor p hpQ]
    exact localDensityFactor_nonneg (p ^ 2) d p
  calc
    (∏ p ∈ Q, localDensityFactor (p ^ 2) d p) =
        ∏ p ∈ Q, quarticSelectedFactor p (A p) := by
      apply Finset.prod_congr rfl
      intro p hpQ
      exact hfactor p hpQ
    _ ≤ Real.exp (-(T * rate) + 2) :=
      quarticSelectedProduct_le_exp Q A T rate
        (fun p hpQ => (hprime p hpQ).pos) hA hnonneg hbias hsquare

/-- Removing the valuation-one correction only increases a selected factor;
the remaining term is exactly the Euler factor of equation (10). -/
theorem quarticSelectedFactor_le_quarticEulerFactor (p : ℕ)
    (hp : 0 < p) (A : ℝ) :
    quarticSelectedFactor p A ≤ quarticEulerFactor p A := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hpne : (p : ℝ) ≠ 0 := hpR.ne'
  have hident : ((p : ℝ) - 1) / (p : ℝ) ^ 2 * A =
      A * ((p : ℝ)⁻¹ - ((p : ℝ) ^ 2)⁻¹) := by
    field_simp
  rw [quarticEulerFactor, hident]
  unfold quarticSelectedFactor
  have hnonneg : 0 ≤ ((p : ℝ) ^ 3)⁻¹ := by positivity
  linarith

/-- The elementary factor bound used for an uncontrolled good prime in
equation (21). -/
theorem quarticSelectedFactor_le_one_add_twentyone_div (p : ℕ)
    (hp : 0 < p) (A : ℝ) (hA : A ≤ 21) :
    quarticSelectedFactor p A ≤ 1 + 21 / (p : ℝ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hpOne : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hpne : (p : ℝ) ≠ 0 := hpR.ne'
  let c : ℝ := ((p : ℝ) - 1) / (p : ℝ) ^ 2
  have hc0 : 0 ≤ c := div_nonneg (by linarith)
    (sq_nonneg _)
  have hcle : c ≤ 1 / (p : ℝ) := by
    dsimp [c]
    field_simp
    linarith
  have h1 : c * A ≤ c * 21 := mul_le_mul_of_nonneg_left hA hc0
  have h2 : c * 21 ≤ 21 / (p : ℝ) := by
    calc
      c * 21 ≤ (1 / (p : ℝ)) * 21 := mul_le_mul_of_nonneg_right hcle (by norm_num)
      _ = 21 / (p : ℝ) := by ring
  calc
    quarticSelectedFactor p A ≤ quarticEulerFactor p A :=
      quarticSelectedFactor_le_quarticEulerFactor p hp A
    _ ≤ 1 + 21 / (p : ℝ) := by
      change 1 + c * A ≤ 1 + 21 / (p : ℝ)
      linarith

/-- A reusable bound for the whole selected-good-prime product from an
explicit trace-sum budget. The unrestricted `|A_p|≤21` bound is sufficient. -/
theorem quarticSelectedProduct_le_exp_trace_budget
    (Q : Finset ℕ) (A : ℕ → ℝ) (S : ℝ)
    (hpos : ∀ p ∈ Q, 0 < p)
    (hA : ∀ p ∈ Q, |A p| ≤ 21)
    (hfactor : ∀ p ∈ Q, 0 ≤ quarticSelectedFactor p (A p))
    (hbudget : (∑ p ∈ Q, A p / (p : ℝ)) +
      21 * ∑ p ∈ Q, (1 : ℝ) / (p : ℝ) ^ 2 ≤ S) :
    (∏ p ∈ Q, quarticSelectedFactor p (A p)) ≤ Real.exp S := by
  have hpoint (p : ℕ) (hpQ : p ∈ Q) :=
    quarticSelectedFactor_le_quarticEulerFactor p (hpos p hpQ) (A p)
  have heulerNonneg (p : ℕ) (hpQ : p ∈ Q) :
      0 ≤ quarticEulerFactor p (A p) :=
    (hfactor p hpQ).trans (hpoint p hpQ)
  calc
    (∏ p ∈ Q, quarticSelectedFactor p (A p)) ≤
        ∏ p ∈ Q, quarticEulerFactor p (A p) :=
      Finset.prod_le_prod₀ hfactor hpoint
    _ ≤ Real.exp ((∑ p ∈ Q, A p / (p : ℝ)) +
          21 * ∑ p ∈ Q, (1 : ℝ) / (p : ℝ) ^ 2) :=
      quarticEulerProduct_le_exp Q A hpos hA heulerNonneg
    _ ≤ Real.exp S := Real.exp_le_exp.mpr hbudget

/-- Logarithmic version of the crude selected-prime product bound. Supplying
`R = log(2B)` and an elementary prime-reciprocal budget gives the good-prime
component of (21). -/
theorem quarticSelectedProduct_le_log_power
    (Q : Finset ℕ) (A : ℕ → ℝ) (S R : ℝ)
    (hR : 0 < R)
    (hpos : ∀ p ∈ Q, 0 < p)
    (hA : ∀ p ∈ Q, |A p| ≤ 21)
    (hfactor : ∀ p ∈ Q, 0 ≤ quarticSelectedFactor p (A p))
    (hbudget : (∑ p ∈ Q, A p / (p : ℝ)) +
      21 * ∑ p ∈ Q, (1 : ℝ) / (p : ℝ) ^ 2 ≤
        S + 21 * Real.log R) :
    (∏ p ∈ Q, quarticSelectedFactor p (A p)) ≤
      Real.exp S * R ^ 21 := by
  calc
    (∏ p ∈ Q, quarticSelectedFactor p (A p)) ≤
        Real.exp (S + 21 * Real.log R) :=
      quarticSelectedProduct_le_exp_trace_budget Q A _ hpos hA hfactor hbudget
    _ = Real.exp S * R ^ 21 := by
      rw [Real.exp_add]
      have h21 : Real.exp ((21 : ℝ) * Real.log R) = R ^ 21 := by
        simpa only [Nat.cast_ofNat, Real.exp_log hR] using
          (Real.exp_nat_mul (Real.log R) 21)
      rw [h21]

/-- Good-prime local-density form of the logarithmic bound used in (21).
The prime-sum budget is explicit, so this theorem can be applied to any
finite selected set without importing a global analytic assertion. -/
theorem selectedLocalDensityProduct_le_log_power
    (Q : Finset ℕ) (d : Fin 4 → ℕ) (A : ℕ → ℝ) (S R : ℝ)
    (hR : 0 < R)
    (hprime : ∀ p ∈ Q, p.Prime)
    (hunit : ∀ p ∈ Q, ∀ i, (d i : ZMod p) ≠ 0)
    (hfour : ∀ p ∈ Q, (4 : ZMod p) ≠ 0)
    (htrace : ∀ p ∈ Q,
      (Nat.card {y : Fin 4 → ZMod p //
        (∑ i, (d i : ZMod p) * y i ^ 4) = 0} : ℝ) /
        (p : ℝ) ^ 3 =
        1 + A p * ((p : ℝ)⁻¹ - ((p : ℝ) ^ 2)⁻¹))
    (hA : ∀ p ∈ Q, |A p| ≤ 21)
    (hbudget : (∑ p ∈ Q, A p / (p : ℝ)) +
      21 * ∑ p ∈ Q, (1 : ℝ) / (p : ℝ) ^ 2 ≤
        S + 21 * Real.log R) :
    (∏ p ∈ Q, localDensityFactor (p ^ 2) d p) ≤
      Real.exp S * R ^ 21 := by
  classical
  have hfactor (p : ℕ) (hpQ : p ∈ Q) :
      localDensityFactor (p ^ 2) d p = quarticSelectedFactor p (A p) := by
    letI : Fact p.Prime := ⟨hprime p hpQ⟩
    have htr :
        (localQuarticCount (ZMod p) 0
          (fun i => (d i : ZMod p)) : ℝ) / (p : ℝ) ^ 3 =
        1 + A p * ((p : ℝ)⁻¹ - ((p : ℝ) ^ 2)⁻¹) := by
      simpa only [localQuarticCount, Nat.card_eq_fintype_card] using
        htrace p hpQ
    simpa only [quarticSelectedFactor] using
      localDensityFactor_good_prime_formula p (hprime p hpQ) d (A p)
        (hunit p hpQ) (hfour p hpQ) htr
  have hnonneg (p : ℕ) (hpQ : p ∈ Q) :
      0 ≤ quarticSelectedFactor p (A p) := by
    rw [← hfactor p hpQ]
    exact localDensityFactor_nonneg (p ^ 2) d p
  calc
    (∏ p ∈ Q, localDensityFactor (p ^ 2) d p) =
        ∏ p ∈ Q, quarticSelectedFactor p (A p) := by
      apply Finset.prod_congr rfl
      intro p hpQ
      exact hfactor p hpQ
    _ ≤ Real.exp S * R ^ 21 :=
      quarticSelectedProduct_le_log_power Q A S R hR
        (fun p hpQ => (hprime p hpQ).pos) hA hnonneg hbudget

end Erdos940.Quartic
