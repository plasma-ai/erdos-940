module

public import Erdos940.Statement
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Data.Finset.NAry
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Group
public import Mathlib.Tactic.Linarith

/-!
# Cube-full parts and small sums for Erdős Problem 940

This file follows Section 2 and equation (3) of Beyer–de Ryke, *A density
deficit for sums of three cube-full numbers*. The analytic estimates and
canonical decomposition below are separate proof obligations. The finite
bound for one- and two-term sums is proved independently of those estimates.
-/

@[expose] public section

namespace Erdos940

/-- Positive cube-full numbers in Beyer–de Ryke's argument. -/
def CubeFull (n : ℕ) : Prop := 0 < n ∧ Nat.Full 3 n

/-- The canonical parameters in Lemma 2.1. -/
structure CanonicalData where
  x : ℕ
  b : ℕ
  c : ℕ
  x_pos : 0 < x
  b_pos : 0 < b
  c_pos : 0 < c
  squarefree_bc : Squarefree (b * c)

def CanonicalData.value (t : CanonicalData) : ℕ :=
  t.x ^ 3 * t.b ^ 4 * t.c ^ 5

/-- Every positive number of the canonical form is cube-full. -/
theorem CanonicalData.cubeFull (t : CanonicalData) : CubeFull t.value := by
  refine ⟨?_, ?_⟩
  · exact Nat.mul_pos
      (Nat.mul_pos (pow_pos t.x_pos 3) (pow_pos t.b_pos 4))
      (pow_pos t.c_pos 5)
  · intro p hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hdiv : p ∣ t.value := Nat.dvd_of_mem_primeFactors hp
    change p ∣ t.x ^ 3 * t.b ^ 4 * t.c ^ 5 at hdiv
    rcases hprime.dvd_mul.mp hdiv with hleft | hc
    · rcases hprime.dvd_mul.mp hleft with hx | hb
      · have hpx : p ∣ t.x := hprime.dvd_of_dvd_pow hx
        exact dvd_mul_of_dvd_left
          (dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd hpx 3) _) _
      · have hpb : p ∣ t.b := hprime.dvd_of_dvd_pow hb
        have hpb3 : p ^ 3 ∣ t.b ^ 4 :=
          pow_dvd_pow_of_dvd_of_le hpb (by decide)
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hpb3 _) _
    · have hpc : p ∣ t.c := hprime.dvd_of_dvd_pow hc
      have hpc3 : p ^ 3 ∣ t.c ^ 5 :=
        pow_dvd_pow_of_dvd_of_le hpc (by decide)
      exact dvd_mul_of_dvd_right hpc3 _

private def cubeExponent (e : ℕ) : ℕ :=
  if e % 3 = 0 then e / 3 else (e - 3) / 3

private def fourthExponent (e : ℕ) : ℕ :=
  if e % 3 = 1 then 1 else 0

private def fifthExponent (e : ℕ) : ℕ :=
  if e % 3 = 2 then 1 else 0

private theorem exponent_split (e : ℕ) (he : e = 0 ∨ 3 ≤ e) :
    e = 3 * cubeExponent e + 4 * fourthExponent e + 5 * fifthExponent e := by
  rcases he with rfl | he
  · simp [cubeExponent, fourthExponent, fifthExponent]
  · simp only [cubeExponent, fourthExponent, fifthExponent]
    split_ifs <;> omega

private theorem partExponents_le_one (e : ℕ) :
    fourthExponent e + fifthExponent e ≤ 1 := by
  simp only [fourthExponent, fifthExponent]
  split_ifs <;> omega

private noncomputable def cubeFactors (n : ℕ) : ℕ →₀ ℕ :=
  Finsupp.mapRange cubeExponent (by simp [cubeExponent]) n.factorization

private noncomputable def fourthFactors (n : ℕ) : ℕ →₀ ℕ :=
  Finsupp.mapRange fourthExponent (by simp [fourthExponent]) n.factorization

private noncomputable def fifthFactors (n : ℕ) : ℕ →₀ ℕ :=
  Finsupp.mapRange fifthExponent (by simp [fifthExponent]) n.factorization

private theorem factors_support_prime (n : ℕ) (f : ℕ → ℕ) (hf : f 0 = 0) :
    ∀ p ∈ (Finsupp.mapRange f hf n.factorization).support, p.Prime := by
  intro p hp
  have hsub : (Finsupp.mapRange f hf n.factorization).support ⊆
      n.factorization.support := Finsupp.support_mapRange
  exact Nat.prime_of_mem_primeFactors (hsub hp)

private theorem factors_product_pos (n : ℕ) (f : ℕ → ℕ) (hf : f 0 = 0) :
    0 < (Finsupp.mapRange f hf n.factorization).prod (· ^ ·) := by
  apply Nat.prod_pow_pos_of_zero_notMem_support
  intro hzero
  exact Nat.not_prime_zero (factors_support_prime n f hf 0 hzero)

private theorem cubeFactors_product_factorization (n : ℕ) :
    ((cubeFactors n).prod (· ^ ·)).factorization = cubeFactors n := by
  exact Nat.prod_pow_factorization_eq_self
    (factors_support_prime n cubeExponent (by simp [cubeExponent]))

private theorem fourthFactors_product_factorization (n : ℕ) :
    ((fourthFactors n).prod (· ^ ·)).factorization = fourthFactors n := by
  exact Nat.prod_pow_factorization_eq_self
    (factors_support_prime n fourthExponent (by simp [fourthExponent]))

private theorem fifthFactors_product_factorization (n : ℕ) :
    ((fifthFactors n).prod (· ^ ·)).factorization = fifthFactors n := by
  exact Nat.prod_pow_factorization_eq_self
    (factors_support_prime n fifthExponent (by simp [fifthExponent]))

/-- Existence in Lemma 2.1, obtained prime by prime from the exponents. -/
theorem exists_canonicalData_of_cubeFull (n : ℕ) (hn : CubeFull n) :
    ∃ t : CanonicalData, t.value = n := by
  have hexp (p : ℕ) : n.factorization p = 0 ∨ 3 ≤ n.factorization p := by
    by_cases hzero : n.factorization p = 0
    · exact Or.inl hzero
    · right
      have hmem : p ∈ n.primeFactors := by
        rw [← Nat.support_factorization]
        exact Finsupp.mem_support_iff.mpr hzero
      have hp : p.Prime := Nat.prime_of_mem_primeFactors hmem
      exact (hp.pow_dvd_iff_le_factorization hn.1.ne').mp (hn.2 p hmem)
  let x := (cubeFactors n).prod (· ^ ·)
  let b := (fourthFactors n).prod (· ^ ·)
  let c := (fifthFactors n).prod (· ^ ·)
  have hx : 0 < x := factors_product_pos n cubeExponent (by simp [cubeExponent])
  have hb : 0 < b := factors_product_pos n fourthExponent (by simp [fourthExponent])
  have hc : 0 < c := factors_product_pos n fifthExponent (by simp [fifthExponent])
  have hxf : x.factorization = cubeFactors n := cubeFactors_product_factorization n
  have hbf : b.factorization = fourthFactors n := fourthFactors_product_factorization n
  have hcf : c.factorization = fifthFactors n := fifthFactors_product_factorization n
  have hsq : Squarefree (b * c) := by
    apply Nat.squarefree_of_factorization_le_one (Nat.mul_ne_zero hb.ne' hc.ne')
    intro p
    rw [Nat.factorization_mul hb.ne' hc.ne', Finsupp.add_apply, hbf, hcf]
    change fourthExponent (n.factorization p) + fifthExponent (n.factorization p) ≤ 1
    exact partExponents_le_one _
  refine ⟨⟨x, b, c, hx, hb, hc, hsq⟩, ?_⟩
  change x ^ 3 * b ^ 4 * c ^ 5 = n
  apply Nat.eq_of_factorization_eq
    (Nat.mul_ne_zero
      (Nat.mul_ne_zero (pow_ne_zero _ hx.ne') (pow_ne_zero _ hb.ne'))
      (pow_ne_zero _ hc.ne')) hn.1.ne'
  intro p
  rw [Nat.factorization_mul
      (Nat.mul_ne_zero (pow_ne_zero _ hx.ne') (pow_ne_zero _ hb.ne'))
      (pow_ne_zero _ hc.ne'),
    Nat.factorization_mul (pow_ne_zero _ hx.ne') (pow_ne_zero _ hb.ne')]
  simp only [Nat.factorization_pow, Finsupp.add_apply, Finsupp.nsmul_apply,
    hxf, hbf, hcf]
  change 3 * cubeExponent (n.factorization p) +
      4 * fourthExponent (n.factorization p) +
      5 * fifthExponent (n.factorization p) = n.factorization p
  exact (exponent_split _ (hexp p)).symm

/-- The prime exponents in a canonical decomposition. -/
private theorem CanonicalData.factorization_value (t : CanonicalData) (p : ℕ) :
    t.value.factorization p =
      3 * t.x.factorization p + 4 * t.b.factorization p +
        5 * t.c.factorization p := by
  rw [show t.value = t.x ^ 3 * t.b ^ 4 * t.c ^ 5 from rfl,
    Nat.factorization_mul
      (Nat.mul_ne_zero (pow_ne_zero _ t.x_pos.ne') (pow_ne_zero _ t.b_pos.ne'))
      (pow_ne_zero _ t.c_pos.ne'),
    Nat.factorization_mul (pow_ne_zero _ t.x_pos.ne') (pow_ne_zero _ t.b_pos.ne')]
  simp [Nat.factorization_pow, Finsupp.add_apply, Finsupp.nsmul_apply, add_assoc]

private theorem CanonicalData.part_factorizations_le_one (t : CanonicalData) (p : ℕ) :
    t.b.factorization p + t.c.factorization p ≤ 1 := by
  have h := t.squarefree_bc.natFactorization_le_one p
  simpa [Nat.factorization_mul t.b_pos.ne' t.c_pos.ne', Finsupp.add_apply] using h

private theorem unique_exponents {x b c x' b' c' : ℕ}
    (h : 3 * x + 4 * b + 5 * c = 3 * x' + 4 * b' + 5 * c')
    (hbc : b + c ≤ 1) (hbc' : b' + c' ≤ 1) :
    x = x' ∧ b = b' ∧ c = c' := by
  omega

/-- Uniqueness in Lemma 2.1. -/
theorem canonicalData_value_injective : Function.Injective CanonicalData.value := by
  intro t u hvalue
  have hcomponents (p : ℕ) :
      t.x.factorization p = u.x.factorization p ∧
      t.b.factorization p = u.b.factorization p ∧
      t.c.factorization p = u.c.factorization p := by
    apply unique_exponents
    · calc
        3 * t.x.factorization p + 4 * t.b.factorization p +
            5 * t.c.factorization p = t.value.factorization p :=
          (t.factorization_value p).symm
        _ = u.value.factorization p := by rw [hvalue]
        _ = 3 * u.x.factorization p + 4 * u.b.factorization p +
            5 * u.c.factorization p := u.factorization_value p
    · exact t.part_factorizations_le_one p
    · exact u.part_factorizations_le_one p
  have hx : t.x = u.x :=
    Nat.eq_of_factorization_eq t.x_pos.ne' u.x_pos.ne' fun p => (hcomponents p).1
  have hb : t.b = u.b :=
    Nat.eq_of_factorization_eq t.b_pos.ne' u.b_pos.ne' fun p => (hcomponents p).2.1
  have hc : t.c = u.c :=
    Nat.eq_of_factorization_eq t.c_pos.ne' u.c_pos.ne' fun p => (hcomponents p).2.2
  cases t with
  | mk x b c x_pos b_pos c_pos squarefree_bc =>
    cases u with
    | mk x' b' c' x_pos' b_pos' c_pos' squarefree_bc' =>
      dsimp at hx hb hc
      subst x'
      subst b'
      subst c'
      rfl

/-- Lemma 2.1: existence and uniqueness of the cube-full decomposition. -/
theorem cubeFull_iff_unique_canonicalData (n : ℕ) :
    CubeFull n ↔ ∃! t : CanonicalData, t.value = n := by
  constructor
  · intro hn
    obtain ⟨t, ht⟩ := exists_canonicalData_of_cubeFull n hn
    refine ⟨t, ht, ?_⟩
    intro t' ht'
    apply canonicalData_value_injective
    exact ht'.trans ht.symm
  · rintro ⟨t, rfl, _⟩
    exact t.cubeFull

/-- The possible 4-full parts of the canonical decomposition. -/
def CanonicalPart (d : ℕ) : Prop :=
  ∃ b c : ℕ, 0 < b ∧ 0 < c ∧ Squarefree (b * c) ∧ d = b ^ 4 * c ^ 5

abbrev CanonicalParts := {d : ℕ // CanonicalPart d}

theorem CanonicalPart.pos {d : ℕ} (hd : CanonicalPart d) : 0 < d := by
  obtain ⟨b, c, hb, hc, _, rfl⟩ := hd
  exact Nat.mul_pos (pow_pos hb 4) (pow_pos hc 5)

theorem CanonicalData.part (t : CanonicalData) :
    CanonicalPart (t.b ^ 4 * t.c ^ 5) :=
  ⟨t.b, t.c, t.b_pos, t.c_pos, t.squarefree_bc, rfl⟩

private noncomputable def primeChoiceWeight (pc : ℕ × Bool) : ℝ :=
  if pc.1.Prime then
    if pc.2 then 3 * (pc.1 : ℝ) ^ (-(5 / 3 : ℝ))
    else 3 * (pc.1 : ℝ) ^ (-(4 / 3 : ℝ))
  else 0

private theorem summable_primeChoiceWeight : Summable primeChoiceWeight := by
  have h4base : Summable (fun p : ℕ => (p : ℝ) ^ (-(4 / 3 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have h5base : Summable (fun p : ℕ => (p : ℝ) ^ (-(5 / 3 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have h4 : Summable (fun p : ℕ =>
      if p.Prime then 3 * (p : ℝ) ^ (-(4 / 3 : ℝ)) else 0) := by
    apply Summable.of_nonneg_of_le
      (fun p => by
        by_cases hp : p.Prime
        · simp [hp, Real.rpow_nonneg]
        · simp [hp])
      (fun p => by
        by_cases hp : p.Prime
        · simp [hp]
        · simp [hp]; positivity)
      (h4base.mul_left 3)
  have h5 : Summable (fun p : ℕ =>
      if p.Prime then 3 * (p : ℝ) ^ (-(5 / 3 : ℝ)) else 0) := by
    apply Summable.of_nonneg_of_le
      (fun p => by
        by_cases hp : p.Prime
        · simp [hp, Real.rpow_nonneg]
        · simp [hp])
      (fun p => by
        by_cases hp : p.Prime
        · simp [hp]
        · simp [hp]; positivity)
      (h5base.mul_left 3)
  apply (summable_prod_of_nonneg (fun pc => by
    unfold primeChoiceWeight
    split_ifs <;> positivity)).mpr
  constructor
  · intro p
    exact (hasSum_fintype (fun y : Bool => primeChoiceWeight (p, y))).summable
  · convert h5.add h4 using 1
    funext p
    by_cases hp : p.Prime <;>
      simp [primeChoiceWeight, hp, tsum_fintype]

private theorem summable_primeChoiceProducts :
    Summable (fun S : Finset (ℕ × Bool) => ∏ pc ∈ S, primeChoiceWeight pc) := by
  apply summable_finsetProd_of_summable_norm
  have hnonneg (pc : ℕ × Bool) : 0 ≤ primeChoiceWeight pc := by
    unfold primeChoiceWeight
    split_ifs <;> positivity
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hnonneg _)] using
    summable_primeChoiceWeight

private noncomputable def partB (d : CanonicalParts) : ℕ :=
  Classical.choose d.property

private noncomputable def partC (d : CanonicalParts) : ℕ :=
  Classical.choose (Classical.choose_spec d.property)

private theorem partBC_spec (d : CanonicalParts) :
    0 < partB d ∧ 0 < partC d ∧ Squarefree (partB d * partC d) ∧
      d.val = partB d ^ 4 * partC d ^ 5 := by
  exact Classical.choose_spec (Classical.choose_spec d.property)

private noncomputable def coloredFactors (d : CanonicalParts) : Finset (ℕ × Bool) := by
  classical
  exact ((partB d).primeFactors.image fun p => (p, false)) ∪
    ((partC d).primeFactors.image fun p => (p, true))

private theorem coloredFactors_injective : Function.Injective coloredFactors := by
  intro d e hcolored
  have hbFactors : (partB d).primeFactors = (partB e).primeFactors := by
    ext p
    have hmem := congrArg (fun S : Finset (ℕ × Bool) => (p, false) ∈ S) hcolored
    simpa [coloredFactors] using hmem
  have hcFactors : (partC d).primeFactors = (partC e).primeFactors := by
    ext p
    have hmem := congrArg (fun S : Finset (ℕ × Bool) => (p, true) ∈ S) hcolored
    simpa [coloredFactors] using hmem
  have hbd : Squarefree (partB d) :=
    (Nat.squarefree_mul_iff.mp (partBC_spec d).2.2.1).2.1
  have hbe : Squarefree (partB e) :=
    (Nat.squarefree_mul_iff.mp (partBC_spec e).2.2.1).2.1
  have hcd : Squarefree (partC d) :=
    (Nat.squarefree_mul_iff.mp (partBC_spec d).2.2.1).2.2
  have hce : Squarefree (partC e) :=
    (Nat.squarefree_mul_iff.mp (partBC_spec e).2.2.1).2.2
  have hb : partB d = partB e := by
    calc
      partB d = ∏ p ∈ (partB d).primeFactors, p :=
        (Nat.prod_primeFactors_of_squarefree hbd).symm
      _ = ∏ p ∈ (partB e).primeFactors, p := by rw [hbFactors]
      _ = partB e := Nat.prod_primeFactors_of_squarefree hbe
  have hc : partC d = partC e := by
    calc
      partC d = ∏ p ∈ (partC d).primeFactors, p :=
        (Nat.prod_primeFactors_of_squarefree hcd).symm
      _ = ∏ p ∈ (partC e).primeFactors, p := by rw [hcFactors]
      _ = partC e := Nat.prod_primeFactors_of_squarefree hce
  apply Subtype.ext
  calc
    d.val = partB d ^ 4 * partC d ^ 5 := (partBC_spec d).2.2.2
    _ = partB e ^ 4 * partC e ^ 5 := by rw [hb, hc]
    _ = e.val := (partBC_spec e).2.2.2.symm

private theorem primeFactor_weight_product (m : ℕ) (hm : Squarefree m) (e : ℝ) :
    (∏ p ∈ m.primeFactors, (3 : ℝ) * (p : ℝ) ^ e) =
      (3 : ℝ) ^ m.primeFactors.card * (m : ℝ) ^ e := by
  rw [Finset.prod_mul_distrib, Finset.prod_const]
  rw [Real.finsetProd_rpow m.primeFactors (fun p => (p : ℝ))
    (by intro p hp; positivity) e]
  rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hm]

private theorem coloredFactors_weight (d : CanonicalParts) :
    (∏ pc ∈ coloredFactors d, primeChoiceWeight pc) =
      (3 : ℝ) ^ d.val.primeFactors.card *
        (d.val : ℝ) ^ (-(1 / 3 : ℝ)) := by
  let b := partB d
  let c := partC d
  have hb : 0 < b := (partBC_spec d).1
  have hc : 0 < c := (partBC_spec d).2.1
  have hbc := Nat.squarefree_mul_iff.mp (partBC_spec d).2.2.1
  have hval : d.val = b ^ 4 * c ^ 5 := (partBC_spec d).2.2.2
  have hdisj : Disjoint (b.primeFactors.image fun p => (p, false))
      (c.primeFactors.image fun p => (p, true)) := by
    apply Finset.disjoint_left.mpr
    intro pc hpc1 hpc2
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hpc1
    obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp hpc2
    simp at heq
  have hprod :
      (∏ pc ∈ coloredFactors d, primeChoiceWeight pc) =
        (∏ p ∈ b.primeFactors, (3 : ℝ) * (p : ℝ) ^ (-(4 / 3 : ℝ))) *
        (∏ p ∈ c.primeFactors, (3 : ℝ) * (p : ℝ) ^ (-(5 / 3 : ℝ))) := by
    change (∏ pc ∈ (b.primeFactors.image fun p => (p, false)) ∪
        (c.primeFactors.image fun p => (p, true)), primeChoiceWeight pc) = _
    rw [Finset.prod_union hdisj]
    rw [Finset.prod_image (by intro x hx y hy h; exact congrArg Prod.fst h),
      Finset.prod_image (by intro x hx y hy h; exact congrArg Prod.fst h)]
    congr 1
    · apply Finset.prod_congr rfl
      intro p hp
      simp [primeChoiceWeight, Nat.prime_of_mem_primeFactors hp]
    · apply Finset.prod_congr rfl
      intro p hp
      simp [primeChoiceWeight, Nat.prime_of_mem_primeFactors hp]
  rw [hprod, primeFactor_weight_product b hbc.2.1,
    primeFactor_weight_product c hbc.2.2]
  have hcard : d.val.primeFactors.card =
      b.primeFactors.card + c.primeFactors.card := by
    rw [hval, Nat.primeFactors_mul (pow_ne_zero _ (by omega : b ≠ 0))
      (pow_ne_zero _ (by omega : c ≠ 0)), Nat.primeFactors_pow b (by norm_num : 4 ≠ 0),
      Nat.primeFactors_pow c (by norm_num : 5 ≠ 0),
      Finset.card_union_of_disjoint hbc.1.disjoint_primeFactors]
  have hbpow : (b : ℝ) ^ (-(4 / 3 : ℝ)) =
      ((b : ℝ) ^ 4) ^ (-(1 / 3 : ℝ)) := by
    calc
      (b : ℝ) ^ (-(4 / 3 : ℝ)) = (b : ℝ) ^ ((4 : ℕ) * (-(1 / 3 : ℝ))) := by
        congr 1; norm_num
      _ = ((b : ℝ) ^ 4) ^ (-(1 / 3 : ℝ)) :=
        Real.rpow_natCast_mul (by positivity) 4 _
  have hcpow : (c : ℝ) ^ (-(5 / 3 : ℝ)) =
      ((c : ℝ) ^ 5) ^ (-(1 / 3 : ℝ)) := by
    calc
      (c : ℝ) ^ (-(5 / 3 : ℝ)) = (c : ℝ) ^ ((5 : ℕ) * (-(1 / 3 : ℝ))) := by
        congr 1; norm_num
      _ = ((c : ℝ) ^ 5) ^ (-(1 / 3 : ℝ)) :=
        Real.rpow_natCast_mul (by positivity) 5 _
  have hweight : (b : ℝ) ^ (-(4 / 3 : ℝ)) * (c : ℝ) ^ (-(5 / 3 : ℝ)) =
      (d.val : ℝ) ^ (-(1 / 3 : ℝ)) := by
    rw [hbpow, hcpow, ← Real.mul_rpow (by positivity) (by positivity)]
    norm_cast
    rw [← hval]
  rw [hcard, pow_add]
  calc
    ((3 : ℝ) ^ b.primeFactors.card * (b : ℝ) ^ (-(4 / 3 : ℝ))) *
        ((3 : ℝ) ^ c.primeFactors.card * (c : ℝ) ^ (-(5 / 3 : ℝ))) =
      ((3 : ℝ) ^ b.primeFactors.card * (3 : ℝ) ^ c.primeFactors.card) *
        ((b : ℝ) ^ (-(4 / 3 : ℝ)) * (c : ℝ) ^ (-(5 / 3 : ℝ))) := by ring
    _ = _ := by rw [hweight]

/-- The factor `3 ^ ω(d)` in equation (2) allows the later local estimate. -/
theorem summable_canonicalPart_weighted :
    Summable (fun d : CanonicalParts =>
      (3 : ℝ) ^ d.val.primeFactors.card * (d.val : ℝ) ^ (-(1 / 3 : ℝ))) := by
  have h := summable_primeChoiceProducts.comp_injective coloredFactors_injective
  exact h.congr (fun d => coloredFactors_weight d)

/-- The unweighted Euler-product series in equation (1). -/
theorem summable_canonicalPart_weight :
    Summable (fun d : CanonicalParts => (d.val : ℝ) ^ (-(1 / 3 : ℝ))) := by
  apply Summable.of_nonneg_of_le
    (fun d => Real.rpow_nonneg (by positivity : 0 ≤ (d.val : ℝ)) _)
    (fun d => ?_) summable_canonicalPart_weighted
  have hpow : 1 ≤ (3 : ℝ) ^ d.val.primeFactors.card := by
    exact one_le_pow₀ (by norm_num)
  have hweight : 0 ≤ (d.val : ℝ) ^ (-(1 / 3 : ℝ)) := by positivity
  nlinarith [mul_nonneg (sub_nonneg.mpr hpow) hweight]

/-- A finite set captures all but an arbitrarily small weighted tail. Its
use as a positive tail estimate also needs `summable_canonicalPart_weighted`. -/
theorem canonicalPart_weighted_tail (ε : ℝ) (hε : 0 < ε) :
    ∃ D : Finset CanonicalParts,
      (∑' d : {d : CanonicalParts // d ∉ D},
        (3 : ℝ) ^ d.val.val.primeFactors.card *
          (d.val.val : ℝ) ^ (-(1 / 3 : ℝ))) < ε := by
  have htend := tendsto_tsum_compl_atTop_zero
    (fun d : CanonicalParts =>
      (3 : ℝ) ^ d.val.primeFactors.card * (d.val : ℝ) ^ (-(1 / 3 : ℝ)))
  exact ((tendsto_order.1 htend).2 ε hε).exists

/-- Positive cube-full numbers below a cutoff. -/
noncomputable def cubeFullBelow (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter CubeFull

private noncomputable def canonicalOf (n : ℕ) : CanonicalData := by
  classical
  exact if h : CubeFull n then Classical.choose (exists_canonicalData_of_cubeFull n h)
    else ⟨1, 1, 1, by decide, by decide, by decide, by simp⟩

private theorem canonicalOf_value (n : ℕ) (hn : CubeFull n) :
    (canonicalOf n).value = n := by
  simp only [canonicalOf, dite_eq_left hn]
  exact Classical.choose_spec (exists_canonicalData_of_cubeFull n hn)

private noncomputable def partOf (n : ℕ) : CanonicalParts :=
  ⟨(canonicalOf n).b ^ 4 * (canonicalOf n).c ^ 5, (canonicalOf n).part⟩

private theorem canonicalOf_value_part (n : ℕ) (hn : CubeFull n) :
    n = (canonicalOf n).x ^ 3 * (partOf n).val := by
  simpa [CanonicalData.value, partOf, mul_assoc] using (canonicalOf_value n hn).symm

private noncomputable def partFiber (N : ℕ) (d : CanonicalParts) : Finset ℕ :=
  (cubeFullBelow N).filter (fun n => partOf n = d)

private theorem partFiber_card_le (N : ℕ) (d : CanonicalParts) :
    ((partFiber N d).card : ℝ) ≤
      (N : ℝ) ^ (1 / 3 : ℝ) * (d.val : ℝ) ^ (-(1 / 3 : ℝ)) := by
  classical
  let y : ℝ := ((N : ℝ) / (d.val : ℝ)) ^ (1 / 3 : ℝ)
  have hdpos : 0 < (d.val : ℝ) := by
    exact_mod_cast CanonicalPart.pos d.property
  have hy : 0 ≤ y := Real.rpow_nonneg (div_nonneg (by positivity) hdpos.le) _
  have hinj : Set.InjOn (fun n : ℕ => (canonicalOf n).x) (partFiber N d) := by
    intro n hn m hm hxm
    have hnn : CubeFull n := (Finset.mem_filter.mp hn).1 |> Finset.mem_filter.mp |>.2
    have hnm : CubeFull m := (Finset.mem_filter.mp hm).1 |> Finset.mem_filter.mp |>.2
    have hpn : partOf n = d := (Finset.mem_filter.mp hn).2
    have hpm : partOf m = d := (Finset.mem_filter.mp hm).2
    change (canonicalOf n).x = (canonicalOf m).x at hxm
    calc
      n = (canonicalOf n).x ^ 3 * (partOf n).val := canonicalOf_value_part n hnn
      _ = (canonicalOf m).x ^ 3 * (partOf m).val := by rw [hxm, hpn, hpm]
      _ = m := (canonicalOf_value_part m hnm).symm
  have hsubset : (partFiber N d).image (fun n : ℕ => (canonicalOf n).x) ⊆
      Finset.Ioc 0 (Nat.floor y) := by
    intro x hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
    have hcube : CubeFull n := (Finset.mem_filter.mp hn).1 |> Finset.mem_filter.mp |>.2
    have hnlt : n < N := Finset.mem_range.mp ((Finset.mem_filter.mp hn).1 |> Finset.mem_filter.mp |>.1)
    have hpart : partOf n = d := (Finset.mem_filter.mp hn).2
    have hxd : (canonicalOf n).x ^ 3 * d.val ≤ N := by
      have hidentity := canonicalOf_value_part n hcube
      rw [hpart] at hidentity
      omega
    have hquot : ((canonicalOf n).x : ℝ) ^ 3 ≤ (N : ℝ) / (d.val : ℝ) := by
      apply (le_div_iff₀ hdpos).2
      exact_mod_cast hxd
    have hroot : ((canonicalOf n).x : ℝ) ≤ y := by
      have hroot' := Real.rpow_le_rpow (by positivity : 0 ≤ ((canonicalOf n).x : ℝ) ^ 3)
        hquot (by norm_num : (0 : ℝ) ≤ 1 / 3)
      have hsimp : (((canonicalOf n).x : ℝ) ^ 3) ^ (1 / 3 : ℝ) =
          ((canonicalOf n).x : ℝ) := by
        convert Real.pow_rpow_inv_natCast (by positivity : 0 ≤ ((canonicalOf n).x : ℝ))
          (by norm_num : (3 : ℕ) ≠ 0) using 1; norm_num
      exact hsimp ▸ hroot'
    exact Finset.mem_Ioc.mpr ⟨(canonicalOf n).x_pos,
      (Nat.le_floor_iff hy).2 hroot⟩
  have hcard : (partFiber N d).card ≤ Nat.floor y := by
    calc
      (partFiber N d).card =
          ((partFiber N d).image (fun n : ℕ => (canonicalOf n).x)).card :=
        (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.Ioc 0 (Nat.floor y)).card := Finset.card_le_card hsubset
      _ = Nat.floor y := by simp
  have hbound : ((partFiber N d).card : ℝ) ≤ y :=
    (Nat.cast_le.mpr hcard).trans (Nat.floor_le hy)
  calc
    ((partFiber N d).card : ℝ) ≤ y := hbound
    _ = (N : ℝ) ^ (1 / 3 : ℝ) * (d.val : ℝ) ^ (-(1 / 3 : ℝ)) := by
      dsimp only [y]
      rw [Real.div_rpow (by positivity) hdpos.le]
      rw [Real.rpow_neg hdpos.le]
      simp [div_eq_mul_inv]

/-- Equation (3), with the convergent weight sum as its constant. -/
theorem cubeFullBelow_card_le_cuberoot :
    ∃ W : ℝ, 0 < W ∧ ∀ N : ℕ,
      ((cubeFullBelow N).card : ℝ) ≤ W * (N : ℝ) ^ (1 / 3 : ℝ) := by
  let w : CanonicalParts → ℝ := fun d =>
    (d.val : ℝ) ^ (-(1 / 3 : ℝ))
  have hw : Summable w := summable_canonicalPart_weight
  have hw0 : ∀ d, 0 ≤ w d := by intro d; positivity
  let W : ℝ := (∑' d, w d) + 1
  have hW : 0 < W := by
    have htsum : 0 ≤ ∑' d, w d := tsum_nonneg hw0
    dsimp [W]
    linarith
  refine ⟨W, hW, ?_⟩
  intro N
  let A := cubeFullBelow N
  let D := A.image partOf
  have hcard : A.card = ∑ d ∈ D, (partFiber N d).card := by
    simpa only [A, D, partFiber] using Finset.card_eq_sum_card_image partOf A
  have hsum : (∑ d ∈ D, w d) ≤ ∑' d, w d :=
    hw.sum_le_tsum D (fun d hd => hw0 d)
  have hN0 : 0 ≤ (N : ℝ) ^ (1 / 3 : ℝ) := by positivity
  calc
    ((cubeFullBelow N).card : ℝ) =
        ∑ d ∈ D, ((partFiber N d).card : ℝ) := by
      exact_mod_cast hcard
    _ ≤ ∑ d ∈ D, (N : ℝ) ^ (1 / 3 : ℝ) * w d := by
      apply Finset.sum_le_sum
      intro d hd
      exact partFiber_card_le N d
    _ = (N : ℝ) ^ (1 / 3 : ℝ) * (∑ d ∈ D, w d) := by
      rw [Finset.mul_sum]
    _ ≤ (N : ℝ) ^ (1 / 3 : ℝ) * (∑' d, w d) :=
      mul_le_mul_of_nonneg_left hsum hN0
    _ ≤ W * (N : ℝ) ^ (1 / 3 : ℝ) := by
      dsimp only [W]
      nlinarith

/-- Values obtained from one or two positive cube-full summands below `N`. -/
noncomputable def oneTwoSumsBelow (N : ℕ) : Finset ℕ := by
  classical
  let A := cubeFullBelow N
  exact A ∪ Finset.image₂ (· + ·) A A

/-- Finite combinatorial bound before applying the cube-full counting estimate. -/
theorem oneTwoSumsBelow_card_le (N : ℕ) :
    (oneTwoSumsBelow N).card ≤
      (cubeFullBelow N).card + (cubeFullBelow N).card ^ 2 := by
  classical
  let A := cubeFullBelow N
  change (A ∪ Finset.image₂ (· + ·) A A).card ≤ A.card + A.card ^ 2
  calc
    (A ∪ Finset.image₂ (· + ·) A A).card
        ≤ A.card + (Finset.image₂ (· + ·) A A).card :=
          Finset.card_union_le _ _
    _ ≤ A.card + A.card * A.card :=
      Nat.add_le_add_left (Finset.card_image₂_le (· + ·) A A) A.card
    _ = A.card + A.card ^ 2 := by rw [pow_two]

/-- The one- and two-term sums in Corollary 1.2 contribute `O(N^(2/3))`. -/
theorem oneTwoSumsBelow_card_le_twoThirds :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      ((oneTwoSumsBelow N).card : ℝ) ≤ C * (N : ℝ) ^ (2 / 3 : ℝ) := by
  obtain ⟨W, hW, hcount⟩ := cubeFullBelow_card_le_cuberoot
  refine ⟨W + W ^ 2 + 1, by positivity, ?_⟩
  intro N
  by_cases hN : N = 0
  · subst N
    simp [oneTwoSumsBelow, cubeFullBelow]
  have hN1 : (1 : ℝ) ≤ N := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN
  let q : ℝ := (N : ℝ) ^ (1 / 3 : ℝ)
  let r : ℝ := (N : ℝ) ^ (2 / 3 : ℝ)
  have hq : 0 ≤ q := Real.rpow_nonneg (by positivity) _
  have hr : 0 ≤ r := Real.rpow_nonneg (by positivity) _
  have hqle : q ≤ r :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have hq2 : q ^ 2 = r := by
    dsimp [q, r]
    rw [← Real.rpow_mul_natCast (by positivity : 0 ≤ (N : ℝ)) (1 / 3 : ℝ) 2]
    norm_num
  have hcard := oneTwoSumsBelow_card_le N
  have hcardReal : ((oneTwoSumsBelow N).card : ℝ) ≤
      ((cubeFullBelow N).card : ℝ) + ((cubeFullBelow N).card : ℝ) ^ 2 := by
    exact_mod_cast hcard
  have hcube : ((cubeFullBelow N).card : ℝ) ≤ W * q := hcount N
  have hcube0 : 0 ≤ ((cubeFullBelow N).card : ℝ) := by positivity
  have hW0 : 0 ≤ W := le_of_lt hW
  have hfirst :
      ((cubeFullBelow N).card : ℝ) + ((cubeFullBelow N).card : ℝ) ^ 2 ≤
        W * q + (W * q) ^ 2 := by
    nlinarith
  calc
    ((oneTwoSumsBelow N).card : ℝ) ≤ W * q + (W * q) ^ 2 :=
      hcardReal.trans hfirst
    _ = W * q + W ^ 2 * r := by rw [mul_pow, hq2]
    _ ≤ W * r + W ^ 2 * r := by nlinarith
    _ = (W + W ^ 2) * r := by ring
    _ ≤ (W + W ^ 2 + 1) * r := by nlinarith

/-- The one- and two-term values grow sublinearly, as required by
`SublinearCount`. -/
theorem oneTwoSumsBelow_eventually_small (C : ℕ) (_hC : 0 < C) :
    ∀ᶠ N in Filter.atTop, C * (oneTwoSumsBelow N).card ≤ N := by
  obtain ⟨K, hK, hbound⟩ := oneTwoSumsBelow_card_le_twoThirds
  have htend : Filter.Tendsto
      (fun N : ℕ => (N : ℝ) ^ (1 / 3 : ℝ)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [htend.eventually_ge_atTop ((C : ℝ) * K),
    Filter.eventually_gt_atTop 0] with N hq hN
  have hN0 : 0 ≤ (N : ℝ) := by positivity
  have hq0 : 0 ≤ (N : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_nonneg hN0 _
  have hq2 : ((N : ℝ) ^ (1 / 3 : ℝ)) ^ 2 =
      (N : ℝ) ^ (2 / 3 : ℝ) := by
    rw [← Real.rpow_mul_natCast hN0 (1 / 3 : ℝ) 2]
    norm_num
  have hq3 : ((N : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = (N : ℝ) := by
    rw [← Real.rpow_mul_natCast hN0 (1 / 3 : ℝ) 3]
    norm_num
  have hsmall : ((C * (oneTwoSumsBelow N).card : ℕ) : ℝ) ≤ (N : ℝ) := by
    calc
      ((C * (oneTwoSumsBelow N).card : ℕ) : ℝ) =
          (C : ℝ) * ((oneTwoSumsBelow N).card : ℝ) := by norm_num
      _ ≤ (C : ℝ) * (K * (N : ℝ) ^ (2 / 3 : ℝ)) := by
        exact mul_le_mul_of_nonneg_left (hbound N) (by positivity)
      _ ≤ ((N : ℝ) ^ (1 / 3 : ℝ)) ^ 3 := by
        rw [← hq2]
        nlinarith [sq_nonneg ((N : ℝ) ^ (1 / 3 : ℝ))]
      _ = N := hq3
  exact_mod_cast hsmall

end Erdos940
