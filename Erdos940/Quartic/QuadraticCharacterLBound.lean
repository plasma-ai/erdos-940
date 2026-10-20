import Erdos940.Quartic.EulerLogComparison
import Erdos940.Quartic.EulerPrimeChebyshev
import Erdos940.Quartic.GaussianLBoundAnalytic
import Erdos940.Quartic.RationalEulerProduct
import Erdos940.Quartic.RationalEulerTail
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# Logarithmic bound for a nonprincipal rational Dirichlet constituent

A nonprincipal Dirichlet character of modulus `q` has zero mean over one
period. Its partial sums are therefore bounded by `q`, uniformly in the
cutoff. Abel summation then bounds its L-series by `2 log q + 8` for real
`1 < σ ≤ 2`.
-/

namespace Erdos940.Quartic

open Finset
open Erdos940.Quartic.GaussianLBoundAnalytic

private theorem jacobi_nonzero_at_modular_unit
    (D : ℕ) (u : (ZMod (4 * D))ˣ) :
    jacobiSym (D : ℤ) (u.val.val) ≠ 0 := by
  have hcop : u.val.val.Coprime (4 * D) := ZMod.val_coe_unit_coprime u
  have hcopD : D.Coprime u.val.val :=
    (hcop.of_dvd_right (by exact ⟨4, by ring⟩)).symm
  have hInt : (D : ℤ).gcd u.val.val = 1 := by
    simpa only [Int.gcd_eq_natAbs, Int.natAbs_natCast]
      using hcopD.gcd_eq_one
  exact jacobiSym.ne_zero hInt

private theorem odd_val_modular_unit
    (D : ℕ) (u : (ZMod (4 * D))ˣ) : Odd u.val.val := by
  have hcop : u.val.val.Coprime (4 * D) := ZMod.val_coe_unit_coprime u
  have hcop2 : u.val.val.Coprime 2 :=
    hcop.of_dvd_right (by exact ⟨2 * D, by ring⟩)
  exact Nat.coprime_two_right.mp hcop2

/-- The Jacobi symbol in the denominator, restricted to units modulo
`4D`, is a character valued in the units of `ℂ`. -/
noncomputable def quadraticJacobiUnitHom (D : ℕ) (_hD : 0 < D) :
    (ZMod (4 * D))ˣ →* ℂˣ where
  toFun u := Units.mk0
    (jacobiSym (D : ℤ) u.val.val : ℂ)
    (by exact_mod_cast jacobi_nonzero_at_modular_unit D u)
  map_one' := by
    apply Units.ext
    change (jacobiSym (D : ℤ) ((1 : ZMod (4 * D)).val) : ℂ) = 1
    rw [ZMod.val_one'' (by omega : 4 * D ≠ 1), jacobiSym.one_right]
    norm_num
  map_mul' := by
    intro u v
    apply Units.ext
    change (jacobiSym (D : ℤ) ((u.val * v.val : ZMod (4 * D))).val : ℂ) =
      (jacobiSym (D : ℤ) u.val.val : ℂ) *
        (jacobiSym (D : ℤ) v.val.val : ℂ)
    have huOdd : Odd u.val.val := odd_val_modular_unit D u
    have hvOdd : Odd v.val.val := odd_val_modular_unit D v
    have hproductOdd : Odd (u.val.val * v.val.val) := huOdd.mul hvOdd
    have huNZ : u.val.val ≠ 0 := by
      obtain ⟨r, hr⟩ := huOdd
      omega
    have hvNZ : v.val.val ≠ 0 := by
      obtain ⟨r, hr⟩ := hvOdd
      omega
    have hperiod := jacobiSym.mod_right (D : ℤ) hproductOdd
    simp only [Int.natAbs_natCast, ZMod.val_mul] at hperiod ⊢
    rw [← hperiod, jacobiSym.mul_right' (D : ℤ)
      huNZ hvNZ]
    norm_cast

/-- The rational quadratic character with modulus `4D`, built from
Jacobi's symbol. Values at nonunits are zero by construction. -/
noncomputable def quadraticJacobiCharacter (D : ℕ) (hD : 0 < D) :
    DirichletCharacter ℂ (4 * D) :=
  MulChar.ofUnitHom (quadraticJacobiUnitHom D hD)

/-- On a unit residue represented by an odd natural number, the
constructed character agrees with the original Jacobi symbol. -/
theorem quadraticJacobiCharacter_apply_coprime
    (D : ℕ) (hD : 0 < D) (n : ℕ)
    (hn : n.Coprime (4 * D)) :
    quadraticJacobiCharacter D hD (n : ZMod (4 * D)) =
      (jacobiSym (D : ℤ) n : ℂ) := by
  have : NeZero (4 * D) := ⟨by omega⟩
  have hodd : Odd n := by
    have hcop2 : n.Coprime 2 :=
      hn.of_dvd_right (by exact ⟨2 * D, by ring⟩)
    exact Nat.coprime_two_right.mp hcop2
  let u : (ZMod (4 * D))ˣ := ZMod.unitOfCoprime n hn
  have hu : (u : ZMod (4 * D)) = (n : ZMod (4 * D)) := by
    simp [u]
  rw [← hu]
  rw [quadraticJacobiCharacter, MulChar.ofUnitHom_coe]
  change ((quadraticJacobiUnitHom D hD u : ℂˣ) : ℂ) = _
  change (jacobiSym (D : ℤ) u.val.val : ℂ) = _
  have hval : u.val.val = n % (4 * D) := by
    rw [show u.val = (n : ZMod (4 * D)) from hu, ZMod.val_natCast]
  rw [hval]
  exact_mod_cast (jacobiSym.mod_right (D : ℤ) hodd).symm

/-- For a prime coprime to `4D`, the constructed character is the
Legendre symbol used by the inert-prime local trace. -/
theorem quadraticJacobiCharacter_prime_eq_legendre
    (D : ℕ) (hD : 0 < D) (p : ℕ) [Fact p.Prime]
    (hp : p.Coprime (4 * D)) :
    quadraticJacobiCharacter D hD (p : ZMod (4 * D)) =
      (legendreSym p D : ℂ) := by
  rw [quadraticJacobiCharacter_apply_coprime D hD p hp]
  exact_mod_cast (jacobiSym.legendreSym.to_jacobiSym p (D : ℤ)).symm

theorem quadraticJacobiCharacter_prime_re_eq_legendre
    (D : ℕ) (hD : 0 < D) (p : ℕ) [Fact p.Prime]
    (hp : p.Coprime (4 * D)) :
    (quadraticJacobiCharacter D hD (p : ZMod (4 * D))).re =
      (legendreSym p D : ℝ) := by
  rw [quadraticJacobiCharacter_prime_eq_legendre D hD p hp]
  norm_cast

theorem odd_prime_coprime_four_mul_of_not_dvd
    (D p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) (hgood : ¬p ∣ D) :
    p.Coprime (4 * D) := by
  apply (Nat.Prime.coprime_iff_not_dvd hp).2
  intro hdiv
  rcases hp.dvd_mul.mp hdiv with hfour | hD
  · have hpow : p ∣ 2 ^ 2 := by norm_num at hfour ⊢; exact hfour
    have htwo : p ∣ 2 := hp.dvd_of_dvd_pow hpow
    exact hodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp htwo)
  · exact hgood hD

/-- Away from the prime two, equality with the Legendre symbol also holds
at primes dividing `D`: both sides then vanish. -/
theorem quadraticJacobiCharacter_odd_prime_eq_legendre
    (D : ℕ) (hD : 0 < D) (p : ℕ) [Fact p.Prime]
    (hodd : p ≠ 2) :
    quadraticJacobiCharacter D hD (p : ZMod (4 * D)) =
      (legendreSym p D : ℂ) := by
  by_cases hgood : ¬p ∣ D
  · exact quadraticJacobiCharacter_prime_eq_legendre D hD p
      (odd_prime_coprime_four_mul_of_not_dvd D p (Fact.out) hodd hgood)
  · have hdiv : p ∣ D := Classical.not_not.mp hgood
    have hdivMod : p ∣ 4 * D := by
      exact dvd_mul_of_dvd_right hdiv 4
    have hnunit : ¬IsUnit (p : ZMod (4 * D)) := by
      intro hu
      have hc : p.Coprime (4 * D) :=
        (ZMod.isUnit_iff_coprime p (4 * D)).mp hu
      exact ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mp hc) hdivMod
    have hchar : quadraticJacobiCharacter D hD (p : ZMod (4 * D)) = 0 :=
      MulChar.map_nonunit _ hnunit
    have hleg : legendreSym p D = 0 := by
      apply (legendreSym.eq_zero_iff p (D : ℤ)).mpr
      simpa using (ZMod.natCast_eq_zero_iff D p).mpr hdiv
    rw [hchar, hleg]
    norm_num

/-- The auxiliary modulus is even, so its character vanishes at two. -/
theorem quadraticJacobiCharacter_two_eq_zero
    (D : ℕ) (hD : 0 < D) :
    quadraticJacobiCharacter D hD (2 : ZMod (4 * D)) = 0 := by
  apply MulChar.map_nonunit
  intro hu
  have hc : (2 : ℕ).Coprime (4 * D) :=
    (ZMod.isUnit_iff_coprime 2 (4 * D)).mp hu
  have hnot : ¬2 ∣ 4 * D :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp hc
  exact hnot ⟨2 * D, by ring⟩

/-- A single negative Legendre value witnesses that the Jacobi character
is nonprincipal. -/
theorem quadraticJacobiCharacter_ne_one_of_legendre_neg_one
    (D : ℕ) (hD : 0 < D) (p : ℕ) [Fact p.Prime]
    (hp : p.Coprime (4 * D)) (hleg : legendreSym p D = -1) :
    quadraticJacobiCharacter D hD ≠ 1 := by
  intro hprincipal
  have hpUnit : IsUnit (p : ZMod (4 * D)) :=
    (ZMod.isUnit_iff_coprime p (4 * D)).mpr hp
  have hvalue := quadraticJacobiCharacter_prime_eq_legendre D hD p hp
  rw [hprincipal, hleg] at hvalue
  rw [MulChar.one_apply hpUnit] at hvalue
  norm_num at hvalue

private theorem periodic_sum_range_eq_mod
    (f : ℕ → ℂ) (q : ℕ) (hq : 0 < q)
    (hperiod : ∀ n, f (n + q) = f n)
    (hzero : (∑ i ∈ Finset.range q, f i) = 0) (n : ℕ) :
    (∑ i ∈ Finset.range n, f i) = ∑ i ∈ Finset.range (n % q), f i := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < q
    · simp [Nat.mod_eq_of_lt hn]
    · have hqn : q ≤ n := Nat.le_of_not_lt hn
      have hsub : n - q < n := Nat.sub_lt (by omega) hq
      have hdecomp : n = q + (n - q) := by omega
      conv_lhs => rw [hdecomp, Finset.sum_range_add]
      have hshift : (∑ i ∈ Finset.range (n - q), f (q + i)) =
          ∑ i ∈ Finset.range (n - q), f i := by
        apply Finset.sum_congr rfl
        intro i _
        simpa only [Nat.add_comm] using hperiod i
      rw [hzero, zero_add, hshift, ih (n - q) hsub]
      have hmod : (n - q) % q = n % q := by
        conv_rhs => rw [hdecomp]
        simp only [Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod]
      rw [hmod]

private theorem periodic_sum_range_norm_le
    (f : ℕ → ℂ) (q : ℕ) (hq : 0 < q)
    (hperiod : ∀ n, f (n + q) = f n)
    (hzero : (∑ i ∈ Finset.range q, f i) = 0)
    (hunit : ∀ n, ‖f n‖ ≤ 1) (n : ℕ) :
    ‖∑ i ∈ Finset.range n, f i‖ ≤ (q : ℝ) := by
  calc
    ‖∑ i ∈ Finset.range n, f i‖ =
        ‖∑ i ∈ Finset.range (n % q), f i‖ := by
      rw [periodic_sum_range_eq_mod f q hq hperiod hzero]
    _ ≤ ∑ i ∈ Finset.range (n % q), ‖f i‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range (n % q), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      exact hunit i
    _ = (n % q : ℕ) := by simp
    _ ≤ q := by exact_mod_cast (Nat.mod_lt n hq).le

private theorem sum_Icc_one_eq_sum_range_succ_of_zero
    (f : ℕ → ℂ) (hf0 : f 0 = 0) (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n, f k) = ∑ k ∈ Finset.range (n + 1), f k := by
  induction n with
  | zero => simp [hf0]
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    exact (Finset.sum_range_succ f (n + 1)).symm

/-- A bounded, zero-mean periodic sequence has an L-series bounded
logarithmically in its period, uniformly as `σ` approaches one. -/
theorem norm_periodic_LSeries_le_two_log_add_eight
    (f : ℕ → ℂ) (q : ℕ) (hq : 0 < q)
    (hperiod : ∀ n, f (n + q) = f n)
    (hzero : (∑ i ∈ Finset.range q, f i) = 0)
    (hf0 : f 0 = 0) (hunit : ∀ n, ‖f n‖ ≤ 1)
    (σ : ℝ) (hσ₁ : 1 < σ) (hσ₂ : σ ≤ 2) :
    ‖LSeries f (σ : ℂ)‖ ≤ 2 * Real.log q + 8 := by
  have hqReal : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hAbs : ∀ n, (∑ k ∈ Finset.Icc 1 n, ‖f k‖) ≤ (n : ℝ) := by
    intro n
    calc
      (∑ k ∈ Finset.Icc 1 n, ‖f k‖) ≤
          ∑ _k ∈ Finset.Icc 1 n, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro k _
        exact hunit k
      _ = (n : ℝ) := by simp
  have hCancel : ∀ t, (q : ℝ) < t →
      ‖∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k‖ ≤
        (q : ℝ) ^ (1 / 2 : ℝ) * t ^ (1 / 2 : ℝ) + q := by
    intro t ht
    have ht0 : 0 ≤ t := by linarith
    have hbase : ‖∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k‖ ≤ (q : ℝ) := by
      rw [sum_Icc_one_eq_sum_range_succ_of_zero f hf0]
      exact periodic_sum_range_norm_le f q hq hperiod hzero hunit _
    have hmul : 0 ≤ (q : ℝ) ^ (1 / 2 : ℝ) * t ^ (1 / 2 : ℝ) := by
      positivity
    linarith
  have h := norm_LSeries_le_log_of_partial_sum_bounds f 1 q σ
    (by norm_num) hqReal hσ₁ hσ₂
    (by intro n; simpa using hAbs n)
    (by intro t ht; simpa using hCancel t ht)
  simpa using h

/-- A nonprincipal complex Dirichlet character has an L-series bounded by
`2 log q + 8` throughout the real interval `1 < σ ≤ 2`. -/
theorem norm_nonprincipal_dirichlet_LSeries_le_two_log_add_eight
    (q : ℕ) (hq : 2 ≤ q) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (σ : ℝ) (hσ₁ : 1 < σ) (hσ₂ : σ ≤ 2) :
    ‖LSeries (fun n : ℕ => χ (n : ZMod q)) (σ : ℂ)‖ ≤
      2 * Real.log q + 8 := by
  classical
  have : NeZero q := ⟨by omega⟩
  have hperiod : ∀ n : ℕ,
      χ ((n + q : ℕ) : ZMod q) = χ (n : ZMod q) := by
    intro n
    simp
  have hzero : (∑ i ∈ Finset.range q, χ (i : ZMod q)) = 0 := by
    have hmean : (∑ x : ZMod q, χ x) = 0 := MulChar.sum_eq_zero_of_ne_one hχ
    have htransport : (∑ i : Fin q, χ ((i : ℕ) : ZMod q)) =
        ∑ x : ZMod q, χ x := by
      have hequiv (i : Fin q) : (ZMod.finEquiv q) i = ((i : ℕ) : ZMod q) := by
        apply ZMod.val_injective
        have hv : ((ZMod.finEquiv q) i).val = i.val := by
          cases q with
          | zero => omega
          | succ q => rfl
        rw [hv]
        simp [ZMod.val_natCast_of_lt i.isLt]
      have hsum := Equiv.sum_comp (ZMod.finEquiv q).toEquiv χ
      change (∑ i : Fin q, χ ((ZMod.finEquiv q) i)) =
        ∑ x : ZMod q, χ x at hsum
      simpa only [hequiv] using hsum
    rw [← Fin.sum_univ_eq_sum_range]
    exact htransport.trans hmean
  have hf0 : χ (0 : ZMod q) = 0 := χ.map_zero' (by omega)
  have hunit : ∀ n : ℕ, ‖χ (n : ZMod q)‖ ≤ 1 := by
    intro n
    exact χ.norm_le_one _
  exact norm_periodic_LSeries_le_two_log_add_eight
    (fun n : ℕ => χ (n : ZMod q)) q (by omega)
    hperiod hzero (by simpa using hf0) hunit σ hσ₁ hσ₂

/-- The concrete rational quadratic constituent, with conductor divisor
`4D`, satisfies a uniform logarithmic bound once a negative Legendre
value witnesses nonprincipality. -/
theorem norm_quadraticJacobi_LSeries_le_two_log_add_eight
    (D : ℕ) (hD : 0 < D) (p : ℕ) [Fact p.Prime]
    (hp : p.Coprime (4 * D)) (hleg : legendreSym p D = -1)
    (σ : ℝ) (hσ₁ : 1 < σ) (hσ₂ : σ ≤ 2) :
    ‖LSeries (fun n : ℕ =>
        quadraticJacobiCharacter D hD (n : ZMod (4 * D))) (σ : ℂ)‖ ≤
      2 * Real.log (4 * D : ℕ) + 8 := by
  exact norm_nonprincipal_dirichlet_LSeries_le_two_log_add_eight
    (4 * D) (by omega) (quadraticJacobiCharacter D hD)
    (quadraticJacobiCharacter_ne_one_of_legendre_neg_one D hD p hp hleg)
    σ hσ₁ hσ₂

/-- Chebyshev's theorem supplies the below-cutoff smoothing premise for
any selected finite set of rational primes. -/
theorem selected_rational_prime_log_sum_le_mul_log
    (S : Finset Nat.Primes) (B : ℝ) (hB : 2 ≤ B)
    (hS : ∀ P ∈ S, (P : ℝ) ≤ B) :
    (∑ P ∈ S, Real.log (P : ℝ) / (P : ℝ)) ≤
      (Real.log 4 * (1 + 1 / Real.log 2)) * Real.log B := by
  let F : Finset ℕ := S.image (fun P : Nat.Primes => (P : ℕ))
  have hF : F ⊆ Nat.primesLE ⌊B⌋₊ := by
    intro p hp
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hp
    apply Nat.mem_primesLE.mpr
    refine ⟨?_, P.property⟩
    exact Nat.le_floor (hS P hP)
  have hnonneg (p : ℕ) (hp : p ∈ Nat.primesLE ⌊B⌋₊) :
      0 ≤ Real.log p / (p : ℝ) := by
    have hpPrime := (Nat.mem_primesLE.mp hp).2
    have hpReal : (1 : ℝ) ≤ p := by exact_mod_cast hpPrime.one_le
    positivity
  calc
    (∑ P ∈ S, Real.log (P : ℝ) / (P : ℝ)) =
        ∑ p ∈ F, Real.log p / (p : ℝ) := by
      unfold F
      rw [Finset.sum_image]
      intro P _ Q _ h
      exact Nat.Primes.coe_nat_injective h
    _ ≤ rationalPrimeLogSum ⌊B⌋₊ := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hF
        (fun p hp _ => hnonneg p hp)
    _ ≤ (Real.log 4 * (1 + 1 / Real.log 2)) * Real.log B :=
      rationalPrimeLogSum_le_mul_log B hB

/-- The rational prime-sum comparison for a nonprincipal Dirichlet
constituent. The Euler first-power identity and tail estimate are stated
explicitly; the character L-series bound and its modulus dependence are
proved above. -/
theorem nonprincipal_dirichlet_finite_prime_sum_le_loglog_modulus
    (q : ℕ) (hq : 2 ≤ q) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (S : Finset Nat.Primes) (B : ℝ) (hBpos : 0 < B)
    (hB : 1 ≤ Real.log B)
    (chebError tailError eulerError : ℝ)
    (hChebBelow :
      (∑ P ∈ S, Real.log (P : ℝ) / (P : ℝ)) ≤
        chebError * Real.log B)
    (hseries : Summable (eulerSmoothedTerm
      (fun P : Nat.Primes => (P : ℝ))
      (fun P => (χ (P : ℕ)).re) B))
    (hTail : -tailError ≤
      ∑' P : (Sᶜ : Set Nat.Primes),
        eulerSmoothedTerm (fun P : Nat.Primes => (P : ℝ))
          (fun P => (χ (P : ℕ)).re) B P)
    (hEuler :
      (∑' P : Nat.Primes,
        eulerSmoothedTerm (fun P : Nat.Primes => (P : ℝ))
          (fun P => (χ (P : ℕ)).re) B P) ≤
        Real.log (1 + ‖LSeries (fun n : ℕ => χ (n : ZMod q))
          ((1 + 1 / Real.log B : ℝ) : ℂ)‖) + eulerError) :
    (∑ P ∈ S, (χ (P : ℕ)).re / (P : ℝ)) ≤
      Real.log (Real.log (2 * (q : ℝ))) +
        (Real.log (2 + 9 / Real.log 2) + chebError + tailError + eulerError) := by
  have hlogB : 0 < Real.log B := by linarith
  have hBreal : 1 < B := (Real.log_pos_iff hBpos.le).mp hlogB
  let σ : ℝ := 1 + 1 / Real.log B
  have hσ₁ : 1 < σ := by
    dsimp [σ]
    have : 0 < 1 / Real.log B := one_div_pos.mpr hlogB
    linarith
  have hσ₂ : σ ≤ 2 := by
    dsimp [σ]
    have hInv : 1 / Real.log B ≤ 1 := (div_le_iff₀ hlogB).2 (by linarith)
    linarith
  have hLSeries := norm_nonprincipal_dirichlet_LSeries_le_two_log_add_eight
    q hq χ hχ σ hσ₁ hσ₂
  let L : ℝ := 1 + ‖LSeries (fun n : ℕ => χ (n : ZMod q)) (σ : ℂ)‖
  let K : ℝ := 2 + 9 / Real.log 2
  have hLpos : 0 < L := by dsimp [L]; positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hKpos : 0 < K := by dsimp [K]; positivity
  have hqReal : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have hqPos : (0 : ℝ) < q := by linarith
  have hlogq : Real.log q ≤ Real.log (2 * (q : ℝ)) :=
    Real.log_le_log hqPos (by nlinarith)
  have hlog2Q : Real.log 2 ≤ Real.log (2 * (q : ℝ)) :=
    Real.log_le_log (by norm_num) (by nlinarith)
  have hLbound : L ≤ K * Real.log (2 * (q : ℝ)) := by
    have hfirst : L ≤ 2 * Real.log q + 9 := by
      dsimp [L, σ]
      linarith [hLSeries]
    have hsecond : 2 * Real.log q + 9 ≤
        (2 + 9 / Real.log 2) * Real.log (2 * (q : ℝ)) := by
      have hratio : 9 ≤ (9 / Real.log 2) * Real.log (2 * (q : ℝ)) := by
        have hmul := mul_le_mul_of_nonneg_left hlog2Q
          (div_nonneg (by norm_num : (0 : ℝ) ≤ 9) hlog2.le)
        have hcancel : (9 / Real.log 2) * Real.log 2 = 9 := by
          field_simp
        linarith
      nlinarith [hlogq]
    exact hfirst.trans hsecond
  have hnorm : ∀ P ∈ S, 1 ≤ (P : ℝ) := by
    intro P _
    exact_mod_cast P.property.one_le
  have hc : ∀ P ∈ S, |(χ (P : ℕ)).re| ≤ 1 := by
    intro P _
    exact (Complex.abs_re_le_norm _).trans (χ.norm_le_one _)
  have hresult := finite_prime_sum_le_loglog_modulus S
    (fun P : Nat.Primes => (P : ℝ))
    (fun P => (χ (P : ℕ)).re) B L K (q : ℝ)
    chebError tailError eulerError hBreal hLpos hKpos hqReal
    hLbound hnorm hc hChebBelow hseries hTail
    (by simpa [L, σ] using hEuler)
  simpa [K] using hresult

/-- The fully instantiated rational prime-sum estimate. The finite set
must contain every prime up to the smoothing cutoff. -/
theorem nonprincipal_dirichlet_prime_sum_le_loglog_modulus
    (q : ℕ) (hq : 2 ≤ q) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (S : Finset Nat.Primes) (B : ℝ) (hB : 2 ≤ B)
    (hlogB : 1 ≤ Real.log B)
    (hBelow : ∀ P ∈ S, (P : ℝ) ≤ B)
    (hCover : ∀ P : Nat.Primes, P ∉ S → B < (P : ℝ)) :
    (∑ P ∈ S, (χ (P : ℕ)).re / (P : ℝ)) ≤
      Real.log (Real.log (2 * (q : ℝ))) +
        (Real.log (2 + 9 / Real.log 2) +
          Real.log 4 * (1 + 1 / Real.log 2) +
          Real.log 4 * (1 + 2 / Real.log 2) +
          reciprocalSquareConstant / 2) := by
  let c : Nat.Primes → ℝ := fun P => (χ (P : ℕ)).re
  have hc : ∀ P, |c P| ≤ 1 := by
    intro P
    exact (Complex.abs_re_le_norm _).trans (χ.norm_le_one _)
  have hB' : 1 < B := by linarith
  let σ : ℝ := 1 + 1 / Real.log B
  have hlogBpos : 0 < Real.log B := by linarith
  have hσ : 1 < σ := by
    dsimp [σ]
    have : 0 < 1 / Real.log B := one_div_pos.mpr hlogBpos
    linarith
  have hLSeries : LSeries (fun n : ℕ => χ (n : ZMod q)) (σ : ℂ) ≠ 0 := by
    have hEuler := DirichletCharacter.LSeries_eulerProduct_exp_log χ
      (by simpa only [Complex.ofReal_re] using hσ : 1 < (σ : ℂ).re)
    rw [← hEuler]
    exact Complex.exp_ne_zero _
  have hLpos : 0 < ‖LSeries (fun n : ℕ => χ (n : ZMod q)) (σ : ℂ)‖ :=
    norm_pos_iff.mpr hLSeries
  have hEuler := rationalDirichletEulerLog_le χ B hB'
  have hEuler' :
      (∑' P : Nat.Primes,
        eulerSmoothedTerm (fun Q : Nat.Primes => (Q : ℝ))
          (fun Q => (χ (Q : ℕ)).re) B P) ≤
        Real.log (1 + ‖LSeries (fun n : ℕ => χ (n : ZMod q))
          ((1 + 1 / Real.log B : ℝ) : ℂ)‖) +
            reciprocalSquareConstant / 2 := by
    have hupper : ‖LSeries (fun n : ℕ => χ (n : ZMod q)) (σ : ℂ)‖ ≤
        1 + ‖LSeries (fun n : ℕ => χ (n : ZMod q)) (σ : ℂ)‖ := by
      linarith
    have hlog := Real.log_le_log hLpos hupper
    dsimp [σ] at hlog
    linarith
  simpa only [c] using
    (nonprincipal_dirichlet_finite_prime_sum_le_loglog_modulus
    q hq χ hχ S B (by linarith) hlogB
    (Real.log 4 * (1 + 1 / Real.log 2))
    (Real.log 4 * (1 + 2 / Real.log 2))
    (reciprocalSquareConstant / 2)
    (selected_rational_prime_log_sum_le_mul_log S B hB hBelow)
    (rationalSmoothedPrime_summable c B hB' hc)
    (rationalSmoothedPrime_tail_lower S B hB hCover c hc)
    hEuler')

/-- A negative Legendre value gives the rational quadratic constituent
the same uniform prime-sum bound, with modulus exactly `4D`. -/
theorem quadraticJacobi_prime_sum_le_loglog_four_mul
    (D : ℕ) (hD : 0 < D) (p : ℕ) [Fact p.Prime]
    (hp : p.Coprime (4 * D)) (hleg : legendreSym p D = -1)
    (S : Finset Nat.Primes) (B : ℝ) (hB : 2 ≤ B)
    (hlogB : 1 ≤ Real.log B)
    (hBelow : ∀ P ∈ S, (P : ℝ) ≤ B)
    (hCover : ∀ P : Nat.Primes, P ∉ S → B < (P : ℝ)) :
    (∑ P ∈ S,
      (quadraticJacobiCharacter D hD (P : ℕ)).re / (P : ℝ)) ≤
      Real.log (Real.log (2 * (4 * D : ℕ))) +
        (Real.log (2 + 9 / Real.log 2) +
          Real.log 4 * (1 + 1 / Real.log 2) +
          Real.log 4 * (1 + 2 / Real.log 2) +
          reciprocalSquareConstant / 2) := by
  exact nonprincipal_dirichlet_prime_sum_le_loglog_modulus
    (4 * D) (by omega) (quadraticJacobiCharacter D hD)
    (quadraticJacobiCharacter_ne_one_of_legendre_neg_one D hD p hp hleg)
    S B hB hlogB hBelow hCover

/-- The rational Legendre trace at odd primes, extended by zero at two. -/
noncomputable def rationalLegendrePrimeValue (D : ℕ) (P : Nat.Primes) : ℝ :=
  if (P : ℕ) = 2 then 0 else (legendreSym (P : ℕ) D : ℝ)

theorem quadraticJacobiCharacter_prime_re_eq_rationalLegendrePrimeValue
    (D : ℕ) (hD : 0 < D) (P : Nat.Primes) :
    (quadraticJacobiCharacter D hD (P : ℕ)).re =
      rationalLegendrePrimeValue D P := by
  classical
  unfold rationalLegendrePrimeValue
  split_ifs with htwo
  · simp [htwo, quadraticJacobiCharacter_two_eq_zero D hD]
  · rw [@quadraticJacobiCharacter_odd_prime_eq_legendre D hD
      (P : ℕ) ⟨P.property⟩ htwo]
    norm_cast

/-- An explicit rational quadratic prime-trace bound, with the harmless
prime two removed by setting its trace to zero. -/
theorem rationalLegendre_prime_sum_le_loglog_four_mul
    (D : ℕ) (hD : 0 < D) (p : ℕ) [Fact p.Prime]
    (hp : p.Coprime (4 * D)) (hleg : legendreSym p D = -1)
    (S : Finset Nat.Primes) (B : ℝ) (hB : 2 ≤ B)
    (hlogB : 1 ≤ Real.log B)
    (hBelow : ∀ P ∈ S, (P : ℝ) ≤ B)
    (hCover : ∀ P : Nat.Primes, P ∉ S → B < (P : ℝ)) :
    (∑ P ∈ S, rationalLegendrePrimeValue D P / (P : ℝ)) ≤
      Real.log (Real.log (2 * (4 * D : ℕ))) +
        (Real.log (2 + 9 / Real.log 2) +
          Real.log 4 * (1 + 1 / Real.log 2) +
          Real.log 4 * (1 + 2 / Real.log 2) +
          reciprocalSquareConstant / 2) := by
  have h := quadraticJacobi_prime_sum_le_loglog_four_mul
    D hD p hp hleg S B hB hlogB hBelow hCover
  simpa only [quadraticJacobiCharacter_prime_re_eq_rationalLegendrePrimeValue]
    using h

end Erdos940.Quartic
