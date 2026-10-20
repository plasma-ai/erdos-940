import Erdos940.Quartic.LocalFactorAssembly
import Erdos940.Quartic.SieveAssembly
import Erdos940.Quartic.ExceptionalElimination
import Erdos940.Quartic.UniversalLocalBound
import Erdos940.Quartic.InertLocalTrace
import Erdos940.Quartic.PrimeHarmonic
import Mathlib.Data.Nat.Sqrt

/-!
# Constructing the quartic sieve progression

The modulus contains 16 and the squares of every odd prime up to the cutoff
and every selected prime. CRT prescribes target 8 modulo 16 and target `p`
modulo each `p²`. These congruences determine the finite CRT progression.
-/

namespace Erdos940.Quartic

open Finset
open scoped Function

/-- Odd base primes through `B`. -/
def quarticBasePrimes (B : ℕ) : Finset ℕ :=
  (Finset.Icc 3 B).filter Nat.Prime

/-- Base and selected rational primes. -/
def quarticSievePrimes (B : ℕ) (Q : Finset ℕ) : Finset ℕ :=
  quarticBasePrimes B ∪ Q

/-- Pairwise-coprime moduli used in the CRT progression. -/
def quarticProgressionModuli (B : ℕ) (Q : Finset ℕ) : Finset ℕ :=
  insert 16 ((quarticSievePrimes B Q).image (fun p => p ^ 2))

theorem quarticSievePrimes_mem_prime_gt_two (B : ℕ) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, q.Prime ∧ 2 < q)
    {p : ℕ} (hp : p ∈ quarticSievePrimes B Q) :
    p.Prime ∧ 2 < p := by
  rcases Finset.mem_union.mp hp with hbase | hselected
  · have h := Finset.mem_filter.mp hbase
    exact ⟨h.2, by have := (Finset.mem_Icc.mp h.1).1; omega⟩
  · exact hQ p hselected

theorem quarticProgressionModuli_pos (B : ℕ) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, q.Prime ∧ 2 < q) :
    ∀ m ∈ quarticProgressionModuli B Q, 0 < m := by
  intro m hm
  rcases Finset.mem_insert.mp hm with rfl | hm
  · decide
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hm
    exact pow_pos (quarticSievePrimes_mem_prime_gt_two B Q hQ hp).1.pos _

theorem quarticProgressionModuli_pairwise_coprime (B : ℕ) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, q.Prime ∧ 2 < q) :
    ∀ m ∈ quarticProgressionModuli B Q,
      ∀ n ∈ quarticProgressionModuli B Q,
        m ≠ n → m.Coprime n := by
  intro m hm n hn hne
  rcases Finset.mem_insert.mp hm with rfl | hm
  · rcases Finset.mem_insert.mp hn with rfl | hn
    · exact False.elim (hne rfl)
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hn
      have hqprime := (quarticSievePrimes_mem_prime_gt_two B Q hQ hq).1
      have hqne : 2 ≠ q := by
        have hgt := (quarticSievePrimes_mem_prime_gt_two B Q hQ hq).2
        omega
      simpa only [show 16 = 2 ^ 4 by decide] using
        Nat.coprime_pow_primes 4 2 Nat.prime_two hqprime hqne
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hm
    rcases Finset.mem_insert.mp hn with rfl | hn
    · have hpprime := (quarticSievePrimes_mem_prime_gt_two B Q hQ hp).1
      have hpne : p ≠ 2 := by
        have hgt := (quarticSievePrimes_mem_prime_gt_two B Q hQ hp).2
        omega
      simpa only [show 16 = 2 ^ 4 by decide] using
        Nat.coprime_pow_primes 2 4 hpprime Nat.prime_two hpne
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hn
      have hpq : p ≠ q := by
        intro heq
        exact hne (by rw [heq])
      exact Nat.coprime_pow_primes 2 2
        (quarticSievePrimes_mem_prime_gt_two B Q hQ hp).1
        (quarticSievePrimes_mem_prime_gt_two B Q hQ hq).1 hpq

/-- Product over the subtype of a finite set of moduli. -/
def quarticCRTModulus (R : Finset ℕ) : ℕ := ∏ m : R, m.val

theorem quarticCRTModulus_eq_quarticModulus (R : Finset ℕ) :
    quarticCRTModulus R = quarticModulus R := by
  simpa [quarticCRTModulus, quarticModulus] using
    (Finset.prod_coe_sort (s := R) (f := id))

noncomputable def quarticCRTEquiv (R : Finset ℕ)
    (hcop : ∀ m ∈ R, ∀ n ∈ R, m ≠ n → m.Coprime n) :
    ZMod (quarticCRTModulus R) ≃+* Π m : R, ZMod m.val := by
  have hpair : Pairwise (Nat.Coprime on (fun m : R => m.val)) := by
    intro m n hne
    exact hcop m.val m.property n.val n.property (by
      intro heq
      exact hne (Subtype.ext heq))
  exact ZMod.prodEquivPi (fun m : R => m.val) hpair

theorem quarticCRTEquiv_apply (R : Finset ℕ)
    (hcop : ∀ m ∈ R, ∀ n ∈ R, m ≠ n → m.Coprime n)
    (z : ZMod (quarticCRTModulus R)) (m : ℕ) (hm : m ∈ R) :
    quarticCRTEquiv R hcop z ⟨m, hm⟩ = (ZMod.cast z : ZMod m) := by
  have hdiv : m ∣ quarticCRTModulus R := by
    unfold quarticCRTModulus
    exact Finset.dvd_prod_of_mem (fun n : R => n.val) (Finset.mem_univ ⟨m, hm⟩)
  exact RingHom.congr_fun (Subsingleton.elim
    ((Pi.evalRingHom (fun _ : R => ZMod _) ⟨m, hm⟩).comp
      (quarticCRTEquiv R hcop).toRingHom)
    (ZMod.castHom hdiv (ZMod m))) z

/-- The finite CRT lift of arbitrary target residues at pairwise-coprime
positive moduli. It is chosen in `[0,M)`. -/
noncomputable def quarticCRTResidue (R : Finset ℕ)
    (hR : ∀ m ∈ R, 0 < m)
    (hcop : ∀ m ∈ R, ∀ n ∈ R, m ≠ n → m.Coprime n)
    (target : ℕ → ℕ) : ℕ := by
  classical
  have hM : 0 < quarticCRTModulus R := by
    unfold quarticCRTModulus
    exact Finset.prod_pos (fun m _ => hR m.val m.property)
  letI : NeZero (quarticCRTModulus R) := ⟨hM.ne'⟩
  let e := quarticCRTEquiv R hcop
  exact (e.symm (fun m => (target m.val : ZMod m.val))).val

theorem quarticCRTResidue_lt (R : Finset ℕ)
    (hR : ∀ m ∈ R, 0 < m)
    (hcop : ∀ m ∈ R, ∀ n ∈ R, m ≠ n → m.Coprime n)
    (target : ℕ → ℕ) :
    quarticCRTResidue R hR hcop target < quarticCRTModulus R := by
  classical
  have hM : 0 < quarticCRTModulus R := by
    unfold quarticCRTModulus
    exact Finset.prod_pos (fun m _ => hR m.val m.property)
  letI : NeZero (quarticCRTModulus R) := ⟨hM.ne'⟩
  letI : NeZero (∏ m : R, m.val) := ⟨by
    simpa only [quarticCRTModulus] using hM.ne'⟩
  unfold quarticCRTResidue
  exact ZMod.val_lt _

theorem quarticCRTResidue_cast (R : Finset ℕ)
    (hR : ∀ m ∈ R, 0 < m)
    (hcop : ∀ m ∈ R, ∀ n ∈ R, m ≠ n → m.Coprime n)
    (target : ℕ → ℕ) (m : ℕ) (hm : m ∈ R) :
    (quarticCRTResidue R hR hcop target : ZMod m) =
      (target m : ZMod m) := by
  classical
  have hM : 0 < quarticCRTModulus R := by
    unfold quarticCRTModulus
    exact Finset.prod_pos (fun n _ => hR n.val n.property)
  letI : NeZero (quarticCRTModulus R) := ⟨hM.ne'⟩
  let e := quarticCRTEquiv R hcop
  let z : ZMod (quarticCRTModulus R) :=
    e.symm (fun n => (target n.val : ZMod n.val))
  have hz : e z ⟨m, hm⟩ = (target m : ZMod m) := by
    change e (e.symm _) ⟨m, hm⟩ = _
    rw [e.apply_symm_apply]
  change (quarticCRTEquiv R hcop) z ⟨m, hm⟩ =
    (target m : ZMod m) at hz
  rw [quarticCRTEquiv_apply] at hz
  change (ZMod.cast z : ZMod m) = (target m : ZMod m) at hz
  have hval : ((z.val : ℕ) : ZMod m) = (target m : ZMod m) := by
    simpa only [ZMod.cast_eq_val] using hz
  simpa [quarticCRTResidue, z, e] using hval

/-- Target 8 at the dyadic modulus and target `p` at a prime-square
modulus. -/
def quarticCRTTarget (m : ℕ) : ℕ :=
  if m = 16 then 8 else Nat.sqrt m

theorem quarticCRTTarget_sixteen : quarticCRTTarget 16 = 8 := by
  simp [quarticCRTTarget]

theorem quarticCRTTarget_prime_square (p : ℕ) (hp : p.Prime) :
    quarticCRTTarget (p ^ 2) = p := by
  have hneq : p ^ 2 ≠ 16 := by
    intro h
    have hp4 : p = 4 := Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0)
      (by simpa only [show 16 = 4 ^ 2 by decide] using h)
    have : ¬Nat.Prime 4 := by decide
    exact this (hp4 ▸ hp)
  simp [quarticCRTTarget, hneq, Nat.sqrt_eq']

def quarticProgressionModulus (B : ℕ) (Q : Finset ℕ) : ℕ :=
  quarticCRTModulus (quarticProgressionModuli B Q)

noncomputable def quarticProgressionResidue (B : ℕ) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, q.Prime ∧ 2 < q) : ℕ :=
  quarticCRTResidue (quarticProgressionModuli B Q)
    (quarticProgressionModuli_pos B Q hQ)
    (quarticProgressionModuli_pairwise_coprime B Q hQ)
    quarticCRTTarget

theorem quarticProgressionModulus_pos (B : ℕ) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, q.Prime ∧ 2 < q) :
    0 < quarticProgressionModulus B Q := by
  unfold quarticProgressionModulus quarticCRTModulus
  exact Finset.prod_pos (fun m _ =>
    quarticProgressionModuli_pos B Q hQ m.val m.property)

theorem quarticProgressionResidue_lt (B : ℕ) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, q.Prime ∧ 2 < q) :
    quarticProgressionResidue B Q hQ < quarticProgressionModulus B Q := by
  exact quarticCRTResidue_lt _
    (quarticProgressionModuli_pos B Q hQ)
    (quarticProgressionModuli_pairwise_coprime B Q hQ) _

theorem quarticProgressionResidue_mod_sixteen (B : ℕ) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, q.Prime ∧ 2 < q) :
    (quarticProgressionResidue B Q hQ : ZMod 16) = 8 := by
  have hmem : 16 ∈ quarticProgressionModuli B Q := by
    exact Finset.mem_insert_self _ _
  simpa [quarticProgressionResidue, quarticCRTTarget_sixteen] using
    quarticCRTResidue_cast (quarticProgressionModuli B Q)
      (quarticProgressionModuli_pos B Q hQ)
      (quarticProgressionModuli_pairwise_coprime B Q hQ)
      quarticCRTTarget 16 hmem

theorem quarticProgressionResidue_mod_prime_square (B : ℕ) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, q.Prime ∧ 2 < q)
    (p : ℕ) (hp : p ∈ quarticSievePrimes B Q) :
    (quarticProgressionResidue B Q hQ : ZMod (p ^ 2)) = p := by
  have hmem : p ^ 2 ∈ quarticProgressionModuli B Q := by
    apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
  have hpprime := (quarticSievePrimes_mem_prime_gt_two B Q hQ hp).1
  simpa only [quarticProgressionResidue, quarticCRTTarget_prime_square p hpprime] using
    quarticCRTResidue_cast (quarticProgressionModuli B Q)
      (quarticProgressionModuli_pos B Q hQ)
      (quarticProgressionModuli_pairwise_coprime B Q hQ)
      quarticCRTTarget (p ^ 2) hmem

/-- The normalized density of a CRT modulus is exactly its finite local
factor product. -/
theorem normalizedQuarticLocalDensity_CRT_eq_prod {R : Finset ℕ}
    (hR : ∀ m ∈ R, 0 < m)
    (hcop : ∀ m ∈ R, ∀ n ∈ R, m ≠ n → m.Coprime n)
    (a : ℕ) (d : Fin 4 → CanonicalParts) :
    normalizedQuarticLocalDensity (quarticModulus R) a d =
      ∏ m ∈ R, localDensityFactor m (fun i => (d i).val) a := by
  have hM : 0 < quarticModulus R := quarticModulus_pos hR
  haveI : NeZero (quarticModulus R) := ⟨hM.ne'⟩
  have hcount :
      (localCount (fun i => (d i).val) (quarticModulus R) a : ℝ) =
        ∏ m ∈ R, (localCountAtModulus (fun i => (d i).val) m a : ℝ) := by
    exact_mod_cast localCount_quarticModulus_eq_prod hR hcop
      (fun i => (d i).val) a
  have hprod : (quarticModulus R : ℝ) = ∏ m ∈ R, (m : ℝ) := by
    simp [quarticModulus]
  unfold normalizedQuarticLocalDensity
  simp only [dif_neg hM.ne']
  simp_rw [localDensityFactor]
  rw [Finset.prod_div_distrib, Finset.prod_pow, ← hcount, ← hprod]

def quarticBaseModuli (B : ℕ) : Finset ℕ :=
  insert 16 ((quarticBasePrimes B).image (fun p => p ^ 2))

def quarticSelectedModuli (Q : Finset ℕ) : Finset ℕ :=
  Q.image (fun p => p ^ 2)

theorem quarticProgressionModuli_eq_union (B : ℕ) (Q : Finset ℕ) :
    quarticProgressionModuli B Q =
      quarticBaseModuli B ∪ quarticSelectedModuli Q := by
  simp [quarticProgressionModuli, quarticSievePrimes,
    quarticBaseModuli, quarticSelectedModuli, Finset.image_union,
    Finset.insert_union]

theorem quarticBaseModuli_disjoint_selected (B : ℕ) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, q.Prime ∧ 2 < q)
    (hfar : ∀ q ∈ Q, B < q) :
    Disjoint (quarticBaseModuli B) (quarticSelectedModuli Q) := by
  classical
  have hbase : Disjoint (quarticBasePrimes B) Q := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hle : p ≤ B := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
    exact (Nat.not_lt_of_ge hle) (hfar p hq)
  have hpow : Function.Injective (fun p : ℕ => p ^ 2) :=
    Nat.pow_left_injective (by decide)
  have himage : Disjoint ((quarticBasePrimes B).image (fun p => p ^ 2))
      (Q.image (fun p => p ^ 2)) :=
    (Finset.disjoint_image hpow).2 hbase
  apply Finset.disjoint_left.mpr
  intro m hm hselected
  rcases Finset.mem_insert.mp hm with rfl | hbaseMod
  · obtain ⟨q, hq, hqeq⟩ := Finset.mem_image.mp hselected
    have hqprime := (hQ q hq).1
    have hq4 : q = 4 := Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0)
      (by simpa only [show 16 = 4 ^ 2 by decide] using hqeq)
    have : ¬Nat.Prime 4 := by decide
    exact this (hq4 ▸ hqprime)
  · exact (Finset.disjoint_left.mp himage) hbaseMod hselected

/-- The base factor keeps the dyadic modulus and all odd prime squares up
to `B`. -/
noncomputable def quarticBaseDensity (B : ℕ) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, q.Prime ∧ 2 < q)
    (d : Fin 4 → CanonicalParts) : ℝ :=
  ∏ m ∈ quarticBaseModuli B,
    localDensityFactor m (fun i => (d i).val)
      (quarticProgressionResidue B Q hQ)

/-- The selected-prime factor, with target `p` modulo each `p²`. -/
noncomputable def quarticSelectedDensity (Q : Finset ℕ)
    (d : Fin 4 → CanonicalParts) : ℝ :=
  ∏ p ∈ Q, localDensityFactor (p ^ 2) (fun i => (d i).val) p

theorem quarticProgression_density_factorization (B : ℕ) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, q.Prime ∧ 2 < q)
    (hfar : ∀ q ∈ Q, B < q)
    (d : Fin 4 → CanonicalParts) :
    normalizedQuarticLocalDensity (quarticProgressionModulus B Q)
      (quarticProgressionResidue B Q hQ) d =
      quarticBaseDensity B Q hQ d * quarticSelectedDensity Q d := by
  classical
  let R := quarticProgressionModuli B Q
  let d₀ : Fin 4 → ℕ := fun i => (d i).val
  let a := quarticProgressionResidue B Q hQ
  have hfull :
      normalizedQuarticLocalDensity (quarticProgressionModulus B Q) a d =
        ∏ m ∈ R, localDensityFactor m d₀ a := by
    change normalizedQuarticLocalDensity (quarticCRTModulus R) a d = _
    rw [quarticCRTModulus_eq_quarticModulus]
    exact normalizedQuarticLocalDensity_CRT_eq_prod
      (quarticProgressionModuli_pos B Q hQ)
      (quarticProgressionModuli_pairwise_coprime B Q hQ) a d
  have hselected :
      (∏ m ∈ quarticSelectedModuli Q, localDensityFactor m d₀ a) =
        quarticSelectedDensity Q d := by
    unfold quarticSelectedDensity quarticSelectedModuli
    rw [Finset.prod_image (Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0)).injOn]
    apply Finset.prod_congr rfl
    intro p hp
    have hpp := (hQ p hp).1
    have hpS : p ∈ quarticSievePrimes B Q :=
      Finset.mem_union_right _ hp
    exact localDensityFactor_congr_target (p ^ 2)
      (pow_ne_zero _ hpp.ne_zero) d₀ a p
      (quarticProgressionResidue_mod_prime_square B Q hQ p hpS)
  rw [hfull]
  change (∏ m ∈ quarticProgressionModuli B Q,
    localDensityFactor m d₀ a) = _
  rw [quarticProgressionModuli_eq_union]
  rw [Finset.prod_union (quarticBaseModuli_disjoint_selected B Q hQ hfar)]
  rw [hselected]
  rfl

theorem quarticProgression_density_eq_dyadic_mul_primeProduct
    (B : ℕ) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, q.Prime ∧ 2 < q)
    (d : Fin 4 → CanonicalParts) :
    normalizedQuarticLocalDensity (quarticProgressionModulus B Q)
      (quarticProgressionResidue B Q hQ) d =
      localDensityFactor 16 (fun i => (d i).val) 8 *
        ∏ p ∈ quarticSievePrimes B Q,
          localDensityFactor (p ^ 2) (fun i => (d i).val) p := by
  classical
  let S := quarticSievePrimes B Q
  let d₀ : Fin 4 → ℕ := fun i => (d i).val
  let a := quarticProgressionResidue B Q hQ
  have hfull :
      normalizedQuarticLocalDensity (quarticProgressionModulus B Q) a d =
        ∏ m ∈ quarticProgressionModuli B Q,
          localDensityFactor m d₀ a := by
    change normalizedQuarticLocalDensity
      (quarticCRTModulus (quarticProgressionModuli B Q)) a d = _
    rw [quarticCRTModulus_eq_quarticModulus]
    exact normalizedQuarticLocalDensity_CRT_eq_prod
      (quarticProgressionModuli_pos B Q hQ)
      (quarticProgressionModuli_pairwise_coprime B Q hQ) a d
  have hnot : 16 ∉ S.image (fun p => p ^ 2) := by
    intro hmem
    obtain ⟨p, hp, hp16⟩ := Finset.mem_image.mp hmem
    have hprime := (quarticSievePrimes_mem_prime_gt_two B Q hQ hp).1
    have hp4 : p = 4 := Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0)
      (by simpa only [show 16 = 4 ^ 2 by decide] using hp16)
    have : ¬Nat.Prime 4 := by decide
    exact this (hp4 ▸ hprime)
  have hinj : Function.Injective (fun p : ℕ => p ^ 2) :=
    Nat.pow_left_injective (by decide)
  rw [hfull]
  change (∏ m ∈ insert 16 (S.image (fun p => p ^ 2)),
    localDensityFactor m d₀ a) = _
  rw [Finset.prod_insert hnot, Finset.prod_image hinj.injOn]
  have h16 : localDensityFactor 16 d₀ a = localDensityFactor 16 d₀ 8 :=
    localDensityFactor_congr_target 16 (by decide) d₀ a 8
      (quarticProgressionResidue_mod_sixteen B Q hQ)
  rw [h16]
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  have hprime := (quarticSievePrimes_mem_prime_gt_two B Q hQ hp).1
  exact localDensityFactor_congr_target (p ^ 2)
    (pow_ne_zero _ hprime.ne_zero) d₀ a p
    (quarticProgressionResidue_mod_prime_square B Q hQ p hp)

/-- Universal density bound reduced to finite good-prime costs. The dyadic
factor and coefficient-prime factors are already discharged. -/
theorem quarticProgression_density_le_finite_cost
    (B : ℕ) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, q.Prime ∧ 2 < q)
    (d : Fin 4 → CanonicalParts)
    (cost : ℕ → ℝ) (H : ℝ)
    (hcost : ∀ p ∈ quarticSievePrimes B Q, 0 ≤ cost p)
    (hgood : ∀ p ∈ quarticSievePrimes B Q,
      (∀ i, ¬p ∣ (d i).val) →
      localDensityFactor (p ^ 2) (fun i => (d i).val) p ≤
        Real.exp (cost p))
    (hbudget : (∑ p ∈ quarticSievePrimes B Q, cost p) ≤ H) :
    normalizedQuarticLocalDensity (quarticProgressionModulus B Q)
      (quarticProgressionResidue B Q hQ) d ≤
        16 * (4 : ℝ) ^ (coefficientProduct d).primeFactors.card *
          Real.exp H := by
  let f : ℕ → ℝ := fun p =>
    localDensityFactor (p ^ 2) (fun i => (d i).val) p
  have hprod :
      (∏ p ∈ quarticSievePrimes B Q, f p) ≤
        (4 : ℝ) ^ (coefficientProduct d).primeFactors.card * Real.exp H := by
    apply quartic_local_product_le_coefficient_weight_exp_cost
      (quarticSievePrimes B Q) d f cost H
    · intro p hp
      exact (quarticSievePrimes_mem_prime_gt_two B Q hQ hp).1
    · intro p hp
      exact localDensityFactor_nonneg (p ^ 2) _ _
    · exact hcost
    · intro p hp _
      letI : Fact p.Prime :=
        ⟨(quarticSievePrimes_mem_prime_gt_two B Q hQ hp).1⟩
      apply localDensityFactor_prime_square_le_four p
        (quarticSievePrimes_mem_prime_gt_two B Q hQ hp).1
      · intro i hdiv
        exact canonicalPart_prime_square_dvd (d i) p
          (quarticSievePrimes_mem_prime_gt_two B Q hQ hp).1 hdiv
      · intro hzero
        have hdiv : p ∣ 4 := (ZMod.natCast_eq_zero_iff 4 p).mp hzero
        have hpgt := (quarticSievePrimes_mem_prime_gt_two B Q hQ hp).2
        have hp2 : p ∣ 2 :=
          (quarticSievePrimes_mem_prime_gt_two B Q hQ hp).1.dvd_of_dvd_pow
            (by simpa only [show 4 = 2 ^ 2 by decide] using hdiv)
        have hpLe : p ≤ 2 := Nat.le_of_dvd (by decide) hp2
        omega
    · exact hgood
    · exact hbudget
  have h16 := localDensityFactor_sixteen_le_sixteen
    (fun i => (d i).val) 8
  have hnonneg : 0 ≤ ∏ p ∈ quarticSievePrimes B Q, f p := by
    apply Finset.prod_nonneg
    intro p hp
    exact localDensityFactor_nonneg (p ^ 2) _ _
  rw [quarticProgression_density_eq_dyadic_mul_primeProduct B Q hQ d]
  exact (mul_le_mul h16 hprod hnonneg (by norm_num)).trans_eq (by ring)

theorem quarticBaseDensity_nonneg (B : ℕ) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, q.Prime ∧ 2 < q)
    (d : Fin 4 → CanonicalParts) :
    0 ≤ quarticBaseDensity B Q hQ d := by
  unfold quarticBaseDensity
  exact Finset.prod_nonneg (by
    intro m hm
    exact localDensityFactor_nonneg m _ _)

theorem quarticSelectedDensity_nonneg (Q : Finset ℕ)
    (d : Fin 4 → CanonicalParts) :
    0 ≤ quarticSelectedDensity Q d := by
  unfold quarticSelectedDensity
  exact Finset.prod_nonneg (by
    intro p hp
    exact localDensityFactor_nonneg (p ^ 2) _ _)

theorem quarticProgressionModulus_dvd_of_mem (B : ℕ) (Q : Finset ℕ)
    {m : ℕ} (hm : m ∈ quarticProgressionModuli B Q) :
    m ∣ quarticProgressionModulus B Q := by
  unfold quarticProgressionModulus quarticCRTModulus
  exact Finset.dvd_prod_of_mem (fun n : quarticProgressionModuli B Q => n.val)
    (Finset.mem_univ ⟨m, hm⟩)

theorem quarticProgressionModulus_sixteen_dvd (B : ℕ) (Q : Finset ℕ) :
    16 ∣ quarticProgressionModulus B Q :=
  quarticProgressionModulus_dvd_of_mem B Q (Finset.mem_insert_self _ _)

theorem quarticProgressionModulus_prime_square_dvd (B : ℕ) (Q : Finset ℕ)
    (p : ℕ) (hp : p ∈ quarticSievePrimes B Q) :
    p ^ 2 ∣ quarticProgressionModulus B Q := by
  apply quarticProgressionModulus_dvd_of_mem B Q
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨p, hp, rfl⟩)

theorem quarticProgressionResidue_mod_sixteen_nat (B : ℕ) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, q.Prime ∧ 2 < q) :
    quarticProgressionResidue B Q hQ % 16 = 8 := by
  have h := (ZMod.natCast_eq_natCast_iff' _ _ _).mp
    (quarticProgressionResidue_mod_sixteen B Q hQ)
  norm_num at h ⊢
  exact h

theorem quarticProgressionResidue_mod_prime_square_nat (B : ℕ) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, q.Prime ∧ 2 < q)
    (p : ℕ) (hp : p ∈ quarticSievePrimes B Q) :
    quarticProgressionResidue B Q hQ % (p ^ 2) = p := by
  have hprime := (quarticSievePrimes_mem_prime_gt_two B Q hQ hp).1
  have hlt : p < p ^ 2 := by
    have hp2 := hprime.two_le
    nlinarith
  have h := (ZMod.natCast_eq_natCast_iff' _ _ _).mp
    (quarticProgressionResidue_mod_prime_square B Q hQ p hp)
  simpa [Nat.mod_eq_of_lt hlt] using h

/-- Every exceptional coefficient tuple with no coefficient prime above the
base cutoff has zero density in the concrete progression. -/
theorem quarticProgression_exceptional_zero (B : ℕ) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, q.Prime ∧ 2 < q)
    (d : Fin 4 → CanonicalParts) (hexceptional : ExceptionalTuple d)
    (hsmall : ¬∃ p ∈ (coefficientProduct d).primeFactors, B < p) :
    normalizedQuarticLocalDensity (quarticProgressionModulus B Q)
      (quarticProgressionResidue B Q hQ) d = 0 := by
  let M := quarticProgressionModulus B Q
  let A := quarticProgressionResidue B Q hQ
  have hM : M ≠ 0 := (quarticProgressionModulus_pos B Q hQ).ne'
  have hD : coefficientProduct d ≠ 0 := by
    have hpos : 0 < coefficientProduct d := by
      unfold coefficientProduct
      exact Finset.prod_pos (fun i _ => CanonicalPart.pos (d i).property)
    omega
  have hoddTargets : ∀ p : ℕ, p.Prime → p ≠ 2 →
      (∃ i : Fin 4, p ∣ (d i).val) →
      p ^ 2 ∣ M ∧ A % (p ^ 2) = p := by
    intro p hp hodd ⟨i, hdiv⟩
    have hpD : p ∣ coefficientProduct d := by
      unfold coefficientProduct
      exact dvd_trans hdiv
        (Finset.dvd_prod_of_mem (fun j => (d j).val) (Finset.mem_univ i))
    have hpMem : p ∈ (coefficientProduct d).primeFactors :=
      hp.mem_primeFactors hpD hD
    have hpB : p ≤ B := by
      by_contra hnot
      exact hsmall ⟨p, hpMem, Nat.lt_of_not_ge hnot⟩
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    have hpBase : p ∈ quarticBasePrimes B :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp3, hpB⟩, hp⟩
    have hpS : p ∈ quarticSievePrimes B Q := Finset.mem_union_left _ hpBase
    exact ⟨quarticProgressionModulus_prime_square_dvd B Q p hpS,
      quarticProgressionResidue_mod_prime_square_nat B Q hQ p hpS⟩
  have hz := exceptionalTuple_localCount_zero d hexceptional M A hM
    (quarticProgressionModulus_sixteen_dvd B Q)
    (quarticProgressionResidue_mod_sixteen_nat B Q hQ) hoddTargets
  simp [normalizedQuarticLocalDensity, M, A, hM, hz]

/-- The precise finite trace and selector inputs needed for the selected
factor estimate. The local trace identity may be supplied by either the
inert-prime quadratic formula or the split-prime character formula. -/
theorem quarticSelectedDensity_le_exp (Q : Finset ℕ)
    (A : (Fin 4 → CanonicalParts) → ℕ → ℝ)
    (rate : (Fin 4 → CanonicalParts) → ℝ)
    (T : ℕ) (d : Fin 4 → CanonicalParts)
    (hprime : ∀ p ∈ Q, p.Prime)
    (hunit : ∀ p ∈ Q, ∀ i, ((d i).val : ZMod p) ≠ 0)
    (hfour : ∀ p ∈ Q, (4 : ZMod p) ≠ 0)
    (htrace : ∀ p ∈ Q,
      (Nat.card {y : Fin 4 → ZMod p //
        (∑ i, ((d i).val : ZMod p) * y i ^ 4) = 0} : ℝ) /
        (p : ℝ) ^ 3 =
        1 + A d p * ((p : ℝ)⁻¹ - ((p : ℝ) ^ 2)⁻¹))
    (hA : ∀ p ∈ Q, -(A d p) ≤ 1)
    (hbias : (∑ p ∈ Q, A d p / (p : ℝ)) ≤
      -((T : ℝ) * rate d) + 1)
    (hsquare : (∑ p ∈ Q, (1 : ℝ) / (p : ℝ) ^ 2) ≤ 1) :
    quarticSelectedDensity Q d ≤
      Real.exp (-((T : ℝ) * rate d) + 2) := by
  exact selectedLocalDensityProduct_le_exp Q (fun i => (d i).val)
    (A d) T (rate d) hprime hunit hfour htrace hA hbias hsquare

/-- The inert-prime trace in the real-valued normalization used by the
selected-factor product. -/
theorem quarticInertRealTrace (p : ℕ) [Fact p.Prime]
    (hmod : p % 4 = 3) (d : Fin 4 → CanonicalParts)
    (hunit : ∀ i, ((d i).val : ZMod p) ≠ 0) :
    (Nat.card {y : Fin 4 → ZMod p //
      (∑ i, ((d i).val : ZMod p) * y i ^ 4) = 0} : ℝ) /
        (p : ℝ) ^ 3 =
      1 + (legendreSym p (coefficientProduct d) : ℝ) *
        ((p : ℝ)⁻¹ - ((p : ℝ) ^ 2)⁻¹) := by
  have hD : ((coefficientProduct d : ℤ) : ZMod p) =
      ∏ i, ((d i).val : ZMod p) := by
    simp [coefficientProduct, Nat.cast_prod]
  have hq := inertLocalDensity_eq_legendre hmod
    (fun i => ((d i).val : ZMod p)) hunit
    (coefficientProduct d : ℤ) hD
  have hr := congrArg (fun x : ℚ => (x : ℝ)) hq
  push_cast at hr
  have hcount :
      (Nat.card {y : Fin 4 → ZMod p //
        (∑ i, ((d i).val : ZMod p) * y i ^ 4) = 0} : ℝ) =
        (localQuarticCount (ZMod p) 0
          (fun i => ((d i).val : ZMod p)) : ℝ) := by
    simp [localQuarticCount, Nat.card_eq_fintype_card]
  rw [hcount]
  have hpR : (p : ℝ) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hident : ((p : ℝ) - 1) / (p : ℝ) ^ 2 *
      (legendreSym p (coefficientProduct d) : ℝ) =
      (legendreSym p (coefficientProduct d) : ℝ) *
        ((p : ℝ)⁻¹ - ((p : ℝ) ^ 2)⁻¹) := by
    field_simp [hpR]
  rwa [hident] at hr

/-- At an inert good prime the valuation-one factor costs at most `1/p`
in the exponential product estimate. -/
theorem quarticInertGoodFactor_le_exp_inv (p : ℕ) (hp : p.Prime)
    (hmod : p % 4 = 3) (d : Fin 4 → CanonicalParts)
    (hunit : ∀ i, ((d i).val : ZMod p) ≠ 0) :
    localDensityFactor (p ^ 2) (fun i => (d i).val) p ≤
      Real.exp ((p : ℝ)⁻¹) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hfour : (4 : ZMod p) ≠ 0 := by
    intro hzero
    have hdiv : p ∣ 4 := (ZMod.natCast_eq_zero_iff 4 p).mp hzero
    have hp2 : p ∣ 2 := hp.dvd_of_dvd_pow
      (by simpa only [show 4 = 2 ^ 2 by decide] using hdiv)
    have hpLe : p ≤ 2 := Nat.le_of_dvd (by decide) hp2
    have hp3 : 3 ≤ p := by omega
    omega
  have hD : ((coefficientProduct d : ℤ) : ZMod p) ≠ 0 := by
    have hprod : (∏ i, ((d i).val : ZMod p)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun i _ => hunit i)
    simpa [coefficientProduct, Nat.cast_prod] using hprod
  have hA : (legendreSym p (coefficientProduct d) : ℝ) ≤ 1 := by
    rcases legendreSym.eq_one_or_neg_one p hD with h | h <;>
      simp [h]
  have htrace :
      (localQuarticCount (ZMod p) 0
        (fun i => ((d i).val : ZMod p)) : ℝ) / (p : ℝ) ^ 3 =
        1 + (legendreSym p (coefficientProduct d) : ℝ) *
          ((p : ℝ)⁻¹ - ((p : ℝ) ^ 2)⁻¹) := by
    simpa only [localQuarticCount, Nat.card_eq_fintype_card] using
      quarticInertRealTrace p hmod d hunit
  have hfactor := localDensityFactor_good_prime_formula p hp
    (fun i => (d i).val)
    (legendreSym p (coefficientProduct d) : ℝ)
    hunit hfour htrace
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpOne : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hdiff0 : 0 ≤ (p : ℝ)⁻¹ - ((p : ℝ) ^ 2)⁻¹ := by
    apply sub_nonneg.mpr
    exact (inv_le_inv₀ (by positivity) hpR).2 (by nlinarith)
  have hterm : (legendreSym p (coefficientProduct d) : ℝ) *
      ((p : ℝ)⁻¹ - ((p : ℝ) ^ 2)⁻¹) ≤
      (p : ℝ)⁻¹ - ((p : ℝ) ^ 2)⁻¹ := by
    simpa using mul_le_mul_of_nonneg_right hA hdiff0
  have hfactorBound :
      localDensityFactor (p ^ 2) (fun i => (d i).val) p ≤
        1 + (p : ℝ)⁻¹ := by
    rw [hfactor]
    have hcorrection : 0 ≤ ((p : ℝ) ^ 3)⁻¹ := by positivity
    have hsqinv : 0 ≤ ((p : ℝ) ^ 2)⁻¹ := by positivity
    linarith
  exact hfactorBound.trans (by simpa [add_comm] using
    (Real.add_one_le_exp ((p : ℝ)⁻¹)))

/-- Explicit universal constant arising from the elementary Chebyshev
prime-harmonic estimate and the dyadic local factor. -/
noncomputable def quarticUniversalBoundConstant : ℝ :=
  16 * Real.exp (21 * (Real.log 4 *
    ((Real.log 2)⁻¹ - Real.log (Real.log 2))))

/-- The universal progression estimate (21), conditional only on the
pointwise 21-term good-prime factor estimate for base primes. The inert
selected-prime factor estimate and prime-harmonic bound are proved above. -/
theorem quarticProgression_density_le_universal
    (B T : ℕ) (Q : Finset ℕ) (hB : 3 ≤ B)
    (hQ : ∀ q ∈ Q, q.Prime ∧ 2 < q)
    (hQmod : ∀ q ∈ Q, q % 4 = 3)
    (hfar : ∀ q ∈ Q, B < q)
    (hQbudget : (∑ q ∈ Q, (q : ℝ)⁻¹) ≤ (T : ℝ) + 1)
    (d : Fin 4 → CanonicalParts)
    (hbaseGood : ∀ p ∈ quarticBasePrimes B,
      (∀ i, ¬p ∣ (d i).val) →
      localDensityFactor (p ^ 2) (fun i => (d i).val) p ≤
        Real.exp (21 / (p : ℝ))) :
    normalizedQuarticLocalDensity (quarticProgressionModulus B Q)
      (quarticProgressionResidue B Q hQ) d ≤
        quarticUniversalBoundConstant * Real.exp ((T : ℝ) + 1) *
          Real.log (2 * (B : ℝ)) ^ (30 : ℕ) *
            (4 : ℝ) ^ (coefficientProduct d).primeFactors.card := by
  classical
  let base := quarticBasePrimes B
  let cost : ℕ → ℝ := fun p =>
    if p ∈ Q then (p : ℝ)⁻¹ else 21 / (p : ℝ)
  have hdisj : Disjoint base Q := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hpB : p ≤ B := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
    exact Nat.not_lt_of_ge hpB (hfar p hq)
  have hbaseSubset : base ⊆ Nat.primesLE B := by
    intro p hp
    have h := Finset.mem_filter.mp hp
    simp only [Nat.mem_primesLE]
    exact ⟨(Finset.mem_Icc.mp h.1).2, h.2⟩
  have hcost : ∀ p ∈ quarticSievePrimes B Q, 0 ≤ cost p := by
    intro p hp
    have hpprime := (quarticSievePrimes_mem_prime_gt_two B Q hQ hp).1
    dsimp [cost]
    split_ifs <;> positivity
  have hgood : ∀ p ∈ quarticSievePrimes B Q,
      (∀ i, ¬p ∣ (d i).val) →
      localDensityFactor (p ^ 2) (fun i => (d i).val) p ≤
        Real.exp (cost p) := by
    intro p hp hunitNat
    by_cases hpQ : p ∈ Q
    · have hunit : ∀ i, ((d i).val : ZMod p) ≠ 0 := by
        intro i hzero
        exact hunitNat i ((ZMod.natCast_eq_zero_iff _ _).mp hzero)
      simpa [cost, hpQ] using
        quarticInertGoodFactor_le_exp_inv p (hQ p hpQ).1
          (hQmod p hpQ) d hunit
    · have hpBase : p ∈ base := by
        rcases Finset.mem_union.mp hp with hb | hq
        · exact hb
        · exact (hpQ hq).elim
      simpa [cost, hpQ] using hbaseGood p hpBase hunitNat
  have hbaseCost : (∑ p ∈ base, cost p) =
      21 * ∑ p ∈ base, (p : ℝ)⁻¹ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    have hnot : p ∉ Q := Finset.disjoint_left.mp hdisj hp
    simp [cost, hnot, div_eq_mul_inv]
  have hQCost : (∑ p ∈ Q, cost p) =
      ∑ p ∈ Q, (p : ℝ)⁻¹ := by
    apply Finset.sum_congr rfl
    intro p hp
    simp [cost, hp]
  have hsum : (∑ p ∈ quarticSievePrimes B Q, cost p) =
      21 * ∑ p ∈ base, (p : ℝ)⁻¹ +
        ∑ p ∈ Q, (p : ℝ)⁻¹ := by
    change (∑ p ∈ base ∪ Q, cost p) = _
    rw [Finset.sum_union hdisj, hbaseCost, hQCost]
  have hfinite := quarticProgression_density_le_finite_cost B Q hQ d
    cost (21 * ∑ p ∈ base, (p : ℝ)⁻¹ +
      ∑ p ∈ Q, (p : ℝ)⁻¹) hcost hgood (le_of_eq hsum)
  have hbaseExp := exp_twenty_one_prime_subset_le_log_pow_thirty
    B base hB hbaseSubset
  have hQExp : Real.exp (∑ p ∈ Q, (p : ℝ)⁻¹) ≤
      Real.exp ((T : ℝ) + 1) := Real.exp_le_exp.mpr hQbudget
  have hlog : 0 ≤ Real.log (2 * (B : ℝ)) ^ (30 : ℕ) := by positivity
  have hweight : 0 ≤ (4 : ℝ) ^ (coefficientProduct d).primeFactors.card := by
    positivity
  calc
    _ ≤ 16 * (4 : ℝ) ^ (coefficientProduct d).primeFactors.card *
        Real.exp (21 * ∑ p ∈ base, (p : ℝ)⁻¹ +
          ∑ p ∈ Q, (p : ℝ)⁻¹) := hfinite
    _ = 16 * (4 : ℝ) ^ (coefficientProduct d).primeFactors.card *
        (Real.exp (21 * ∑ p ∈ base, (p : ℝ)⁻¹) *
          Real.exp (∑ p ∈ Q, (p : ℝ)⁻¹)) := by rw [Real.exp_add]
    _ ≤ 16 * (4 : ℝ) ^ (coefficientProduct d).primeFactors.card *
        ((Real.exp (21 * (Real.log 4 *
          ((Real.log 2)⁻¹ - Real.log (Real.log 2)))) *
            Real.log (2 * (B : ℝ)) ^ (30 : ℕ)) *
          Real.exp ((T : ℝ) + 1)) := by
      gcongr
    _ = _ := by unfold quarticUniversalBoundConstant; ring

/-- Assemble the concrete CRT progression for the regular class
`¬ ExceptionalTuple`. The remaining hypotheses are finite local estimates:
the base Euler factor estimate, the selected trace/bias data, and the
universal finite-product estimate. No global moment estimate is assumed. -/
noncomputable def quarticSieveProgressionOfLocalBounds
    (rate : (Fin 4 → CanonicalParts) → ℝ)
    (Creg Cuniv : ℝ) (T B : ℕ) (E : Finset CanonicalParts)
    (Q : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime ∧ 2 < q)
    (hfar : ∀ q ∈ Q, B < q)
    (A : (Fin 4 → CanonicalParts) → ℕ → ℝ)
    (hunit : ∀ d, ¬ExceptionalTuple d → (∀ i, d i ∈ E) →
      ∀ p ∈ Q, ∀ i, ((d i).val : ZMod p) ≠ 0)
    (hfour : ∀ p ∈ Q, (4 : ZMod p) ≠ 0)
    (htrace : ∀ d, ¬ExceptionalTuple d → (∀ i, d i ∈ E) →
      ∀ p ∈ Q,
      (Nat.card {y : Fin 4 → ZMod p //
        (∑ i, ((d i).val : ZMod p) * y i ^ 4) = 0} : ℝ) /
          (p : ℝ) ^ 3 =
          1 + A d p * ((p : ℝ)⁻¹ - ((p : ℝ) ^ 2)⁻¹))
    (hA : ∀ d, ¬ExceptionalTuple d → (∀ i, d i ∈ E) →
      ∀ p ∈ Q, -(A d p) ≤ 1)
    (hbias : ∀ d, ¬ExceptionalTuple d → (∀ i, d i ∈ E) →
      (∑ p ∈ Q, A d p / (p : ℝ)) ≤ -((T : ℝ) * rate d) + 1)
    (hsquare : (∑ p ∈ Q, (1 : ℝ) / (p : ℝ) ^ 2) ≤ 1)
    (hbase : ∀ d, ¬ExceptionalTuple d →
      quarticBaseDensity B Q hQ d ≤ Creg *
        (4 : ℝ) ^ (coefficientProduct d).primeFactors.card *
          Real.log (2 * (coefficientProduct d : ℝ)) ^ (11 : ℕ))
    (huniv : ∀ d,
      quarticBaseDensity B Q hQ d * quarticSelectedDensity Q d ≤
        Cuniv * Real.exp ((T : ℝ) + 1) *
          Real.log (2 * (B : ℝ)) ^ (30 : ℕ) *
            (4 : ℝ) ^ (coefficientProduct d).primeFactors.card) :
    QuarticSieveProgression (fun d => ¬ExceptionalTuple d)
      rate Creg Cuniv T B E where
  M := quarticProgressionModulus B Q
  a := quarticProgressionResidue B Q hQ
  Mpos := quarticProgressionModulus_pos B Q hQ
  aLt := quarticProgressionResidue_lt B Q hQ
  baseDensity := quarticBaseDensity B Q hQ
  selectedDensity := quarticSelectedDensity Q
  base_nonneg := quarticBaseDensity_nonneg B Q hQ
  selected_nonneg := quarticSelectedDensity_nonneg Q
  density_factorization := quarticProgression_density_factorization B Q hQ hfar
  bound15 := hbase
  bound20 := by
    intro d hreg hE
    exact quarticSelectedDensity_le_exp Q A rate T d
      (fun p hp => (hQ p hp).1)
      (hunit d hreg hE) hfour (htrace d hreg hE)
      (hA d hreg hE) (hbias d hreg hE) hsquare
  bound21 := by
    intro d
    rw [quarticProgression_density_factorization B Q hQ hfar]
    exact huniv d
  exceptional_zero8 := by
    intro d hnot hsmall
    exact quarticProgression_exceptional_zero B Q hQ d
      (Classical.not_not.mp hnot) hsmall

/-- Concrete progression constructor with no universal-product hypothesis.
The finite 21-term good-prime bound is the only remaining input for (21). -/
noncomputable def quarticSieveProgressionOfBaseGoodBounds
    (rate : (Fin 4 → CanonicalParts) → ℝ)
    (Creg : ℝ) (T B : ℕ) (E : Finset CanonicalParts)
    (Q : Finset ℕ) (hB : 3 ≤ B)
    (hQ : ∀ q ∈ Q, q.Prime ∧ 2 < q)
    (hQmod : ∀ q ∈ Q, q % 4 = 3)
    (hfar : ∀ q ∈ Q, B < q)
    (hQbudget : (∑ q ∈ Q, (q : ℝ)⁻¹) ≤ (T : ℝ) + 1)
    (A : (Fin 4 → CanonicalParts) → ℕ → ℝ)
    (hunit : ∀ d, ¬ExceptionalTuple d → (∀ i, d i ∈ E) →
      ∀ p ∈ Q, ∀ i, ((d i).val : ZMod p) ≠ 0)
    (hfour : ∀ p ∈ Q, (4 : ZMod p) ≠ 0)
    (htrace : ∀ d, ¬ExceptionalTuple d → (∀ i, d i ∈ E) →
      ∀ p ∈ Q,
      (Nat.card {y : Fin 4 → ZMod p //
        (∑ i, ((d i).val : ZMod p) * y i ^ 4) = 0} : ℝ) /
          (p : ℝ) ^ 3 =
          1 + A d p * ((p : ℝ)⁻¹ - ((p : ℝ) ^ 2)⁻¹))
    (hA : ∀ d, ¬ExceptionalTuple d → (∀ i, d i ∈ E) →
      ∀ p ∈ Q, -(A d p) ≤ 1)
    (hbias : ∀ d, ¬ExceptionalTuple d → (∀ i, d i ∈ E) →
      (∑ p ∈ Q, A d p / (p : ℝ)) ≤ -((T : ℝ) * rate d) + 1)
    (hsquare : (∑ p ∈ Q, (1 : ℝ) / (p : ℝ) ^ 2) ≤ 1)
    (hbase : ∀ d, ¬ExceptionalTuple d →
      quarticBaseDensity B Q hQ d ≤ Creg *
        (4 : ℝ) ^ (coefficientProduct d).primeFactors.card *
          Real.log (2 * (coefficientProduct d : ℝ)) ^ (11 : ℕ))
    (hbaseGood : ∀ (d : Fin 4 → CanonicalParts), ∀ p ∈ quarticBasePrimes B,
      (∀ i, ¬p ∣ (d i).val) →
      localDensityFactor (p ^ 2) (fun i => (d i).val) p ≤
        Real.exp (21 / (p : ℝ))) :
    QuarticSieveProgression (fun d => ¬ExceptionalTuple d) rate
      Creg quarticUniversalBoundConstant T B E := by
  apply quarticSieveProgressionOfLocalBounds rate Creg
    quarticUniversalBoundConstant T B E Q hQ hfar A
    hunit hfour htrace hA hbias hsquare hbase
  intro d
  rw [← quarticProgression_density_factorization B Q hQ hfar]
  exact quarticProgression_density_le_universal B T Q hB hQ
    hQmod hfar hQbudget d (hbaseGood d)

end Erdos940.Quartic
