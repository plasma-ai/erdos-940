import Erdos940.Statement
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic.Linarith

/-!
# Canonical parts of positive 4-powerful numbers

The prime exponents of the coefficient in the unique decomposition
`n = x ^ 4 * b ^ 5 * c ^ 6 * d ^ 7` are 0, 5, 6, or 7. The factors `b`, `c`,
and `d` are pairwise coprime and squarefree, expressed by the squarefreeness
of their product. This is the arithmetic starting point of the quartic
complement proof; no density assertion is made here.
-/

namespace Erdos940.Quartic

/-- Positive 4-powerful natural numbers. -/
def FourFull (n : ℕ) : Prop := 0 < n ∧ Nat.Full 4 n

/-- Unique factorization parameters for a positive 4-powerful number. -/
structure CanonicalData where
  x : ℕ
  b : ℕ
  c : ℕ
  d : ℕ
  x_pos : 0 < x
  b_pos : 0 < b
  c_pos : 0 < c
  d_pos : 0 < d
  squarefree_bcd : Squarefree (b * c * d)

def CanonicalData.value (t : CanonicalData) : ℕ :=
  t.x ^ 4 * t.b ^ 5 * t.c ^ 6 * t.d ^ 7

private def xExponent (e : ℕ) : ℕ :=
  if e % 4 = 0 then e / 4 else (e - 4) / 4

private def bExponent (e : ℕ) : ℕ := if e % 4 = 1 then 1 else 0
private def cExponent (e : ℕ) : ℕ := if e % 4 = 2 then 1 else 0
private def dExponent (e : ℕ) : ℕ := if e % 4 = 3 then 1 else 0

private theorem exponent_split (e : ℕ) (he : e = 0 ∨ 4 ≤ e) :
    e = 4 * xExponent e + 5 * bExponent e +
      6 * cExponent e + 7 * dExponent e := by
  rcases he with rfl | he
  · simp [xExponent, bExponent, cExponent, dExponent]
  · simp only [xExponent, bExponent, cExponent, dExponent]
    split_ifs <;> omega

private theorem partExponents_le_one (e : ℕ) :
    bExponent e + cExponent e + dExponent e ≤ 1 := by
  simp only [bExponent, cExponent, dExponent]
  split_ifs <;> omega

private noncomputable def xFactors (n : ℕ) : ℕ →₀ ℕ :=
  Finsupp.mapRange xExponent (by simp [xExponent]) n.factorization

private noncomputable def bFactors (n : ℕ) : ℕ →₀ ℕ :=
  Finsupp.mapRange bExponent (by simp [bExponent]) n.factorization

private noncomputable def cFactors (n : ℕ) : ℕ →₀ ℕ :=
  Finsupp.mapRange cExponent (by simp [cExponent]) n.factorization

private noncomputable def dFactors (n : ℕ) : ℕ →₀ ℕ :=
  Finsupp.mapRange dExponent (by simp [dExponent]) n.factorization

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

private theorem factors_product_factorization (n : ℕ) (f : ℕ → ℕ)
    (hf : f 0 = 0) :
    ((Finsupp.mapRange f hf n.factorization).prod (· ^ ·)).factorization =
      Finsupp.mapRange f hf n.factorization := by
  exact Nat.prod_pow_factorization_eq_self (factors_support_prime n f hf)

/-- Every positive 4-powerful number has canonical parameters. -/
theorem exists_canonicalData_of_fourFull (n : ℕ) (hn : FourFull n) :
    ∃ t : CanonicalData, t.value = n := by
  have hexp (p : ℕ) : n.factorization p = 0 ∨ 4 ≤ n.factorization p := by
    by_cases hzero : n.factorization p = 0
    · exact Or.inl hzero
    · right
      have hmem : p ∈ n.primeFactors := by
        rw [← Nat.support_factorization]
        exact Finsupp.mem_support_iff.mpr hzero
      have hp : p.Prime := Nat.prime_of_mem_primeFactors hmem
      exact (hp.pow_dvd_iff_le_factorization hn.1.ne').mp (hn.2 p hmem)
  let x := (xFactors n).prod (· ^ ·)
  let b := (bFactors n).prod (· ^ ·)
  let c := (cFactors n).prod (· ^ ·)
  let d := (dFactors n).prod (· ^ ·)
  have hx : 0 < x := factors_product_pos n xExponent (by simp [xExponent])
  have hb : 0 < b := factors_product_pos n bExponent (by simp [bExponent])
  have hc : 0 < c := factors_product_pos n cExponent (by simp [cExponent])
  have hd : 0 < d := factors_product_pos n dExponent (by simp [dExponent])
  have hxf : x.factorization = xFactors n :=
    factors_product_factorization n xExponent (by simp [xExponent])
  have hbf : b.factorization = bFactors n :=
    factors_product_factorization n bExponent (by simp [bExponent])
  have hcf : c.factorization = cFactors n :=
    factors_product_factorization n cExponent (by simp [cExponent])
  have hdf : d.factorization = dFactors n :=
    factors_product_factorization n dExponent (by simp [dExponent])
  have hsq : Squarefree (b * c * d) := by
    apply Nat.squarefree_of_factorization_le_one
      (Nat.mul_ne_zero (Nat.mul_ne_zero hb.ne' hc.ne') hd.ne')
    intro p
    rw [Nat.factorization_mul (Nat.mul_ne_zero hb.ne' hc.ne') hd.ne',
      Nat.factorization_mul hb.ne' hc.ne', Finsupp.add_apply, Finsupp.add_apply,
      hbf, hcf, hdf]
    change bExponent (n.factorization p) + cExponent (n.factorization p) +
      dExponent (n.factorization p) ≤ 1
    exact partExponents_le_one _
  refine ⟨⟨x, b, c, d, hx, hb, hc, hd, hsq⟩, ?_⟩
  change x ^ 4 * b ^ 5 * c ^ 6 * d ^ 7 = n
  apply Nat.eq_of_factorization_eq
    (Nat.mul_ne_zero
      (Nat.mul_ne_zero
        (Nat.mul_ne_zero (pow_ne_zero _ hx.ne') (pow_ne_zero _ hb.ne'))
        (pow_ne_zero _ hc.ne')) (pow_ne_zero _ hd.ne')) hn.1.ne'
  intro p
  rw [Nat.factorization_mul
      (Nat.mul_ne_zero
        (Nat.mul_ne_zero (pow_ne_zero _ hx.ne') (pow_ne_zero _ hb.ne'))
        (pow_ne_zero _ hc.ne')) (pow_ne_zero _ hd.ne'),
    Nat.factorization_mul
      (Nat.mul_ne_zero (pow_ne_zero _ hx.ne') (pow_ne_zero _ hb.ne'))
      (pow_ne_zero _ hc.ne'),
    Nat.factorization_mul (pow_ne_zero _ hx.ne') (pow_ne_zero _ hb.ne')]
  simp only [Nat.factorization_pow, Finsupp.add_apply, Finsupp.nsmul_apply,
    hxf, hbf, hcf, hdf]
  change 4 * xExponent (n.factorization p) +
      5 * bExponent (n.factorization p) +
      6 * cExponent (n.factorization p) +
      7 * dExponent (n.factorization p) = n.factorization p
  exact (exponent_split _ (hexp p)).symm

/-- The canonical parameters always give a positive 4-powerful value. -/
theorem CanonicalData.fourFull (t : CanonicalData) : FourFull t.value := by
  refine ⟨?_, ?_⟩
  · exact Nat.mul_pos
      (Nat.mul_pos
        (Nat.mul_pos (pow_pos t.x_pos 4) (pow_pos t.b_pos 5))
        (pow_pos t.c_pos 6)) (pow_pos t.d_pos 7)
  · intro p hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hdiv : p ∣ t.value := Nat.dvd_of_mem_primeFactors hp
    change p ∣ t.x ^ 4 * t.b ^ 5 * t.c ^ 6 * t.d ^ 7 at hdiv
    rcases hprime.dvd_mul.mp hdiv with hleft | hd
    · rcases hprime.dvd_mul.mp hleft with hleft | hc
      · rcases hprime.dvd_mul.mp hleft with hx | hb
        · exact dvd_mul_of_dvd_left
            (dvd_mul_of_dvd_left
              (dvd_mul_of_dvd_left
                (pow_dvd_pow_of_dvd (hprime.dvd_of_dvd_pow hx) 4) _) _) _
        · exact dvd_mul_of_dvd_left
            (dvd_mul_of_dvd_left
              (dvd_mul_of_dvd_right
                (pow_dvd_pow_of_dvd_of_le (hprime.dvd_of_dvd_pow hb)
                  (by decide : 4 ≤ 5)) _) _) _
      · exact dvd_mul_of_dvd_left
          (dvd_mul_of_dvd_right
            (pow_dvd_pow_of_dvd_of_le (hprime.dvd_of_dvd_pow hc)
              (by decide : 4 ≤ 6)) _) _
    · exact dvd_mul_of_dvd_right
        (pow_dvd_pow_of_dvd_of_le (hprime.dvd_of_dvd_pow hd)
          (by decide : 4 ≤ 7)) _

private theorem CanonicalData.factorization_value (t : CanonicalData) (p : ℕ) :
    t.value.factorization p =
      4 * t.x.factorization p + 5 * t.b.factorization p +
        6 * t.c.factorization p + 7 * t.d.factorization p := by
  rw [show t.value = t.x ^ 4 * t.b ^ 5 * t.c ^ 6 * t.d ^ 7 from rfl,
    Nat.factorization_mul
      (Nat.mul_ne_zero
        (Nat.mul_ne_zero (pow_ne_zero _ t.x_pos.ne')
          (pow_ne_zero _ t.b_pos.ne')) (pow_ne_zero _ t.c_pos.ne'))
      (pow_ne_zero _ t.d_pos.ne'),
    Nat.factorization_mul
      (Nat.mul_ne_zero (pow_ne_zero _ t.x_pos.ne')
        (pow_ne_zero _ t.b_pos.ne')) (pow_ne_zero _ t.c_pos.ne'),
    Nat.factorization_mul (pow_ne_zero _ t.x_pos.ne')
      (pow_ne_zero _ t.b_pos.ne')]
  simp [Nat.factorization_pow, Finsupp.add_apply, Finsupp.nsmul_apply, add_assoc]

private theorem CanonicalData.part_factorizations_le_one (t : CanonicalData)
    (p : ℕ) :
    t.b.factorization p + t.c.factorization p + t.d.factorization p ≤ 1 := by
  have h := t.squarefree_bcd.natFactorization_le_one p
  simpa [Nat.factorization_mul t.b_pos.ne' t.c_pos.ne',
    Nat.factorization_mul (Nat.mul_ne_zero t.b_pos.ne' t.c_pos.ne')
      t.d_pos.ne', Finsupp.add_apply] using h

private theorem unique_exponents {x b c d x' b' c' d' : ℕ}
    (h : 4 * x + 5 * b + 6 * c + 7 * d =
      4 * x' + 5 * b' + 6 * c' + 7 * d')
    (hparts : b + c + d ≤ 1) (hparts' : b' + c' + d' ≤ 1) :
    x = x' ∧ b = b' ∧ c = c' ∧ d = d' := by
  have hb : b = 0 ∨ b = 1 := by omega
  have hc : c = 0 ∨ c = 1 := by omega
  have hd : d = 0 ∨ d = 1 := by omega
  have hb' : b' = 0 ∨ b' = 1 := by omega
  have hc' : c' = 0 ∨ c' = 1 := by omega
  have hd' : d' = 0 ∨ d' = 1 := by omega
  rcases hb with hb | hb <;> rcases hc with hc | hc <;>
    rcases hd with hd | hd <;> rcases hb' with hb' | hb' <;>
    rcases hc' with hc' | hc' <;> rcases hd' with hd' | hd' <;>
    subst_vars <;> omega

/-- The canonical parameters are determined uniquely by their value. -/
theorem canonicalData_value_injective : Function.Injective CanonicalData.value := by
  intro t u hvalue
  have hcomponents (p : ℕ) :
      t.x.factorization p = u.x.factorization p ∧
      t.b.factorization p = u.b.factorization p ∧
      t.c.factorization p = u.c.factorization p ∧
      t.d.factorization p = u.d.factorization p := by
    apply unique_exponents
    · calc
        4 * t.x.factorization p + 5 * t.b.factorization p +
            6 * t.c.factorization p + 7 * t.d.factorization p =
              t.value.factorization p := (t.factorization_value p).symm
        _ = u.value.factorization p := by rw [hvalue]
        _ = 4 * u.x.factorization p + 5 * u.b.factorization p +
            6 * u.c.factorization p + 7 * u.d.factorization p :=
          u.factorization_value p
    · exact t.part_factorizations_le_one p
    · exact u.part_factorizations_le_one p
  have hx : t.x = u.x :=
    Nat.eq_of_factorization_eq t.x_pos.ne' u.x_pos.ne' fun p => (hcomponents p).1
  have hb : t.b = u.b :=
    Nat.eq_of_factorization_eq t.b_pos.ne' u.b_pos.ne' fun p => (hcomponents p).2.1
  have hc : t.c = u.c :=
    Nat.eq_of_factorization_eq t.c_pos.ne' u.c_pos.ne' fun p => (hcomponents p).2.2.1
  have hd : t.d = u.d :=
    Nat.eq_of_factorization_eq t.d_pos.ne' u.d_pos.ne' fun p => (hcomponents p).2.2.2
  cases t with
  | mk x b c d x_pos b_pos c_pos d_pos squarefree_bcd =>
    cases u with
    | mk x' b' c' d' x_pos' b_pos' c_pos' d_pos' squarefree_bcd' =>
      dsimp at hx hb hc hd
      subst x'
      subst b'
      subst c'
      subst d'
      rfl

/-- Existence and uniqueness of the canonical quartic decomposition. -/
theorem fourFull_iff_unique_canonicalData (n : ℕ) :
    FourFull n ↔ ∃! t : CanonicalData, t.value = n := by
  constructor
  · intro hn
    obtain ⟨t, ht⟩ := exists_canonicalData_of_fourFull n hn
    refine ⟨t, ht, ?_⟩
    intro t' ht'
    exact canonicalData_value_injective (ht'.trans ht.symm)
  · rintro ⟨t, rfl, _⟩
    exact t.fourFull

/-- A positive coefficient with prime exponents in `{0,5,6,7}`. -/
def CanonicalPart (a : ℕ) : Prop :=
  ∃ b c d : ℕ, 0 < b ∧ 0 < c ∧ 0 < d ∧
    Squarefree (b * c * d) ∧ a = b ^ 5 * c ^ 6 * d ^ 7

abbrev CanonicalParts := {a : ℕ // CanonicalPart a}

theorem CanonicalPart.pos {a : ℕ} (ha : CanonicalPart a) : 0 < a := by
  obtain ⟨b, c, d, hb, hc, hd, _, rfl⟩ := ha
  exact Nat.mul_pos (Nat.mul_pos (pow_pos hb 5) (pow_pos hc 6)) (pow_pos hd 7)

theorem CanonicalData.part (t : CanonicalData) :
    CanonicalPart (t.b ^ 5 * t.c ^ 6 * t.d ^ 7) :=
  ⟨t.b, t.c, t.d, t.b_pos, t.c_pos, t.d_pos, t.squarefree_bcd, rfl⟩

private noncomputable def partB (a : CanonicalParts) : ℕ :=
  Classical.choose a.property

private noncomputable def partC (a : CanonicalParts) : ℕ :=
  Classical.choose (Classical.choose_spec a.property)

private noncomputable def partD (a : CanonicalParts) : ℕ :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec a.property))

private theorem partBCD_spec (a : CanonicalParts) :
    0 < partB a ∧ 0 < partC a ∧ 0 < partD a ∧
      Squarefree (partB a * partC a * partD a) ∧
      a.val = partB a ^ 5 * partC a ^ 6 * partD a ^ 7 := by
  exact Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec a.property))

private noncomputable def partTriple (a : CanonicalParts) : ℕ × (ℕ × ℕ) :=
  (partB a, (partC a, partD a))

private theorem partTriple_injective : Function.Injective partTriple := by
  intro a a' h
  have hb : partB a = partB a' := congrArg Prod.fst h
  have hc : partC a = partC a' := congrArg (fun z : ℕ × (ℕ × ℕ) => z.2.1) h
  have hd : partD a = partD a' := congrArg (fun z : ℕ × (ℕ × ℕ) => z.2.2) h
  apply Subtype.ext
  calc
    a.val = partB a ^ 5 * partC a ^ 6 * partD a ^ 7 := (partBCD_spec a).2.2.2.2
    _ = partB a' ^ 5 * partC a' ^ 6 * partD a' ^ 7 := by rw [hb, hc, hd]
    _ = a'.val := (partBCD_spec a').2.2.2.2.symm

private noncomputable def tripleWeight (t : ℕ × (ℕ × ℕ)) : ℝ :=
  (t.1 : ℝ) ^ (-(5 / 4 : ℝ)) *
    ((t.2.1 : ℝ) ^ (-(6 / 4 : ℝ)) * (t.2.2 : ℝ) ^ (-(7 / 4 : ℝ)))

private theorem summable_tripleWeight : Summable tripleWeight := by
  have hb : Summable (fun b : ℕ => (b : ℝ) ^ (-(5 / 4 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hc : Summable (fun c : ℕ => (c : ℝ) ^ (-(6 / 4 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hd : Summable (fun d : ℕ => (d : ℝ) ^ (-(7 / 4 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hcd : Summable (fun t : ℕ × ℕ =>
      (t.1 : ℝ) ^ (-(6 / 4 : ℝ)) * (t.2 : ℝ) ^ (-(7 / 4 : ℝ))) :=
    hc.mul_of_nonneg hd (fun _ => by positivity) (fun _ => by positivity)
  exact hb.mul_of_nonneg hcd (fun _ => by positivity) (fun _ => by positivity)

private theorem tripleWeight_partTriple (a : CanonicalParts) :
    tripleWeight (partTriple a) = (a.val : ℝ) ^ (-(1 / 4 : ℝ)) := by
  have hb : 0 ≤ (partB a : ℝ) := by positivity
  have hc : 0 ≤ (partC a : ℝ) := by positivity
  have hd : 0 ≤ (partD a : ℝ) := by positivity
  have hval : (a.val : ℝ) =
      (partB a : ℝ) ^ 5 * (partC a : ℝ) ^ 6 * (partD a : ℝ) ^ 7 := by
    exact_mod_cast (partBCD_spec a).2.2.2.2
  simp only [tripleWeight, partTriple]
  rw [hval, Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) (by positivity)]
  rw [← Real.rpow_natCast_mul hb 5,
    ← Real.rpow_natCast_mul hc 6,
    ← Real.rpow_natCast_mul hd 7]
  norm_num
  ring

/-- The coefficient weights needed to count 4-powerful numbers are summable. -/
theorem summable_canonicalPart_weight :
    Summable (fun a : CanonicalParts => (a.val : ℝ) ^ (-(1 / 4 : ℝ))) := by
  have h := summable_tripleWeight.comp_injective partTriple_injective
  exact h.congr (fun a => tripleWeight_partTriple a)

private noncomputable def tripleWeightExponent
    (s : ℝ) (t : ℕ × (ℕ × ℕ)) : ℝ :=
  (t.1 : ℝ) ^ (-(5 * s)) *
    ((t.2.1 : ℝ) ^ (-(6 * s)) * (t.2.2 : ℝ) ^ (-(7 * s)))

private theorem summable_tripleWeightExponent (s : ℝ) (hs : 1 / 5 < s) :
    Summable (tripleWeightExponent s) := by
  have hb : Summable (fun b : ℕ => (b : ℝ) ^ (-(5 * s))) :=
    Real.summable_nat_rpow.mpr (by nlinarith)
  have hc : Summable (fun c : ℕ => (c : ℝ) ^ (-(6 * s))) :=
    Real.summable_nat_rpow.mpr (by nlinarith)
  have hd : Summable (fun d : ℕ => (d : ℝ) ^ (-(7 * s))) :=
    Real.summable_nat_rpow.mpr (by nlinarith)
  have hcd : Summable (fun t : ℕ × ℕ =>
      (t.1 : ℝ) ^ (-(6 * s)) * (t.2 : ℝ) ^ (-(7 * s))) :=
    hc.mul_of_nonneg hd (fun _ => by positivity) (fun _ => by positivity)
  exact hb.mul_of_nonneg hcd (fun _ => by positivity) (fun _ => by positivity)

private theorem tripleWeightExponent_partTriple (s : ℝ) (a : CanonicalParts) :
    tripleWeightExponent s (partTriple a) = (a.val : ℝ) ^ (-s) := by
  have hb : 0 ≤ (partB a : ℝ) := by positivity
  have hc : 0 ≤ (partC a : ℝ) := by positivity
  have hd : 0 ≤ (partD a : ℝ) := by positivity
  have hval : (a.val : ℝ) =
      (partB a : ℝ) ^ 5 * (partC a : ℝ) ^ 6 * (partD a : ℝ) ^ 7 := by
    exact_mod_cast (partBCD_spec a).2.2.2.2
  simp only [tripleWeightExponent, partTriple]
  rw [hval, Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) (by positivity)]
  rw [← Real.rpow_natCast_mul hb 5,
    ← Real.rpow_natCast_mul hc 6,
    ← Real.rpow_natCast_mul hd 7]
  ring_nf

/-- The coefficient Dirichlet series converges for every exponent above
`1/5`; in particular, a small positive power of a coefficient can be
absorbed into its unweighted `1/4`-power weight. -/
theorem summable_canonicalPart_rpow (s : ℝ) (hs : 1 / 5 < s) :
    Summable (fun a : CanonicalParts => (a.val : ℝ) ^ (-s)) := by
  have h := (summable_tripleWeightExponent s hs).comp_injective
    partTriple_injective
  exact h.congr (tripleWeightExponent_partTriple s)

private noncomputable def coloredFactors (a : CanonicalParts) :
    Finset (ℕ × Fin 3) := by
  classical
  exact ((partB a).primeFactors.image fun p => (p, 0)) ∪
    ((partC a).primeFactors.image fun p => (p, 1)) ∪
    ((partD a).primeFactors.image fun p => (p, 2))

private theorem coloredFactors_injective : Function.Injective coloredFactors := by
  intro a a' hcolored
  have hbFactors : (partB a).primeFactors = (partB a').primeFactors := by
    ext p
    have h := congrArg (fun S : Finset (ℕ × Fin 3) => (p, 0) ∈ S) hcolored
    simpa [coloredFactors] using h
  have hcFactors : (partC a).primeFactors = (partC a').primeFactors := by
    ext p
    have h := congrArg (fun S : Finset (ℕ × Fin 3) => (p, 1) ∈ S) hcolored
    simpa [coloredFactors] using h
  have hdFactors : (partD a).primeFactors = (partD a').primeFactors := by
    ext p
    have h := congrArg (fun S : Finset (ℕ × Fin 3) => (p, 2) ∈ S) hcolored
    simpa [coloredFactors] using h
  have hsq (z : CanonicalParts) :
      Squarefree (partB z) ∧ Squarefree (partC z) ∧
        Squarefree (partD z) := by
    have hsplit := Nat.squarefree_mul_iff.mp (partBCD_spec z).2.2.2.1
    have hbc := Nat.squarefree_mul_iff.mp hsplit.2.1
    exact ⟨hbc.2.1, hbc.2.2, hsplit.2.2⟩
  have hb : partB a = partB a' := by
    calc
      partB a = ∏ p ∈ (partB a).primeFactors, p :=
        (Nat.prod_primeFactors_of_squarefree (hsq a).1).symm
      _ = ∏ p ∈ (partB a').primeFactors, p := by rw [hbFactors]
      _ = partB a' := Nat.prod_primeFactors_of_squarefree (hsq a').1
  have hc : partC a = partC a' := by
    calc
      partC a = ∏ p ∈ (partC a).primeFactors, p :=
        (Nat.prod_primeFactors_of_squarefree (hsq a).2.1).symm
      _ = ∏ p ∈ (partC a').primeFactors, p := by rw [hcFactors]
      _ = partC a' := Nat.prod_primeFactors_of_squarefree (hsq a').2.1
  have hd : partD a = partD a' := by
    calc
      partD a = ∏ p ∈ (partD a).primeFactors, p :=
        (Nat.prod_primeFactors_of_squarefree (hsq a).2.2).symm
      _ = ∏ p ∈ (partD a').primeFactors, p := by rw [hdFactors]
      _ = partD a' := Nat.prod_primeFactors_of_squarefree (hsq a').2.2
  apply Subtype.ext
  calc
    a.val = partB a ^ 5 * partC a ^ 6 * partD a ^ 7 :=
      (partBCD_spec a).2.2.2.2
    _ = partB a' ^ 5 * partC a' ^ 6 * partD a' ^ 7 := by rw [hb, hc, hd]
    _ = a'.val := (partBCD_spec a').2.2.2.2.symm

private noncomputable def primeChoiceWeight (s : ℝ) (pc : ℕ × Fin 3) : ℝ :=
  if pc.1.Prime then
    (4 : ℝ) * (pc.1 : ℝ) ^ (-((5 + pc.2.val : ℕ) : ℝ) * s)
  else 0

private theorem summable_primeChoiceWeight (s : ℝ) (hs : 1 / 5 < s) :
    Summable (primeChoiceWeight s) := by
  have hcolor (j : Fin 3) :
      Summable (fun p : ℕ => primeChoiceWeight s (p, j)) := by
    have hbase : Summable (fun p : ℕ =>
        (p : ℝ) ^ (-((5 + j.val : ℕ) : ℝ) * s)) :=
      Real.summable_nat_rpow.mpr (by
        have hs0 : 0 < s := by linarith
        have hcoeff : (5 : ℝ) ≤ ((5 + j.val : ℕ) : ℝ) := by
          exact_mod_cast Nat.le_add_right 5 j.val
        nlinarith [mul_nonneg (sub_nonneg.mpr hcoeff) hs0.le])
    apply Summable.of_nonneg_of_le
      (fun p => by
        unfold primeChoiceWeight
        split_ifs <;> positivity)
      (fun p => by
        unfold primeChoiceWeight
        split_ifs <;> simp <;> positivity)
      (hbase.mul_left 4)
  apply (summable_prod_of_nonneg (fun pc => by
    unfold primeChoiceWeight
    split_ifs <;> positivity)).mpr
  constructor
  · intro p
    exact (hasSum_fintype (fun j : Fin 3 => primeChoiceWeight s (p, j))).summable
  · convert ((hcolor 0).add (hcolor 1)).add (hcolor 2) using 1
    funext p
    simp only [tsum_fintype, Fin.sum_univ_three]

private theorem summable_primeChoiceProducts (s : ℝ) (hs : 1 / 5 < s) :
    Summable (fun S : Finset (ℕ × Fin 3) =>
      ∏ pc ∈ S, primeChoiceWeight s pc) := by
  apply summable_finsetProd_of_summable_norm
  have hnonneg (pc : ℕ × Fin 3) : 0 ≤ primeChoiceWeight s pc := by
    unfold primeChoiceWeight
    split_ifs <;> positivity
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hnonneg _)] using
    summable_primeChoiceWeight s hs

private theorem primeFactor_weight_product
    (m : ℕ) (hm : Squarefree m) (e : ℝ) :
    (∏ p ∈ m.primeFactors, (4 : ℝ) * (p : ℝ) ^ e) =
      (4 : ℝ) ^ m.primeFactors.card * (m : ℝ) ^ e := by
  rw [Finset.prod_mul_distrib, Finset.prod_const]
  rw [Real.finsetProd_rpow m.primeFactors (fun p => (p : ℝ))
    (by intro p hp; positivity) e]
  rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hm]

private theorem coloredFactors_weight (s : ℝ) (a : CanonicalParts) :
    (∏ pc ∈ coloredFactors a, primeChoiceWeight s pc) =
      (4 : ℝ) ^ a.val.primeFactors.card * (a.val : ℝ) ^ (-s) := by
  let b := partB a
  let c := partC a
  let d := partD a
  have hb : 0 < b := (partBCD_spec a).1
  have hc : 0 < c := (partBCD_spec a).2.1
  have hd : 0 < d := (partBCD_spec a).2.2.1
  have hval : a.val = b ^ 5 * c ^ 6 * d ^ 7 := (partBCD_spec a).2.2.2.2
  have hsplit := Nat.squarefree_mul_iff.mp (partBCD_spec a).2.2.2.1
  have hbc := Nat.squarefree_mul_iff.mp hsplit.2.1
  have hdisjBC : Disjoint (b.primeFactors.image fun p => (p, (0 : Fin 3)))
      (c.primeFactors.image fun p => (p, (1 : Fin 3))) := by
    apply Finset.disjoint_left.mpr
    intro pc hpc0 hpc1
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hpc0
    obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp hpc1
    simp at heq
  have hdisjD : Disjoint
      ((b.primeFactors.image fun p => (p, (0 : Fin 3))) ∪
        (c.primeFactors.image fun p => (p, (1 : Fin 3))))
      (d.primeFactors.image fun p => (p, (2 : Fin 3))) := by
    apply Finset.disjoint_left.mpr
    intro pc hpc01 hpc2
    obtain hpc0 | hpc1 := Finset.mem_union.mp hpc01
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hpc0
      obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp hpc2
      simp at heq
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hpc1
      obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp hpc2
      simp at heq
  have hprod :
      (∏ pc ∈ coloredFactors a, primeChoiceWeight s pc) =
        (∏ p ∈ b.primeFactors, (4 : ℝ) * (p : ℝ) ^ (-(5 * s))) *
        (∏ p ∈ c.primeFactors, (4 : ℝ) * (p : ℝ) ^ (-(6 * s))) *
        (∏ p ∈ d.primeFactors, (4 : ℝ) * (p : ℝ) ^ (-(7 * s))) := by
    change (∏ pc ∈
      ((b.primeFactors.image fun p => (p, (0 : Fin 3))) ∪
        (c.primeFactors.image fun p => (p, (1 : Fin 3)))) ∪
        (d.primeFactors.image fun p => (p, (2 : Fin 3))),
        primeChoiceWeight s pc) = _
    rw [Finset.prod_union hdisjD, Finset.prod_union hdisjBC]
    rw [Finset.prod_image (by intro x hx y hy h; exact congrArg Prod.fst h),
      Finset.prod_image (by intro x hx y hy h; exact congrArg Prod.fst h),
      Finset.prod_image (by intro x hx y hy h; exact congrArg Prod.fst h)]
    congr 1
    · congr 1
      · apply Finset.prod_congr rfl
        intro p hp
        simp [primeChoiceWeight, Nat.prime_of_mem_primeFactors hp]
      · apply Finset.prod_congr rfl
        intro p hp
        simp [primeChoiceWeight, Nat.prime_of_mem_primeFactors hp]
    · apply Finset.prod_congr rfl
      intro p hp
      simp [primeChoiceWeight, Nat.prime_of_mem_primeFactors hp]
  have hcard : a.val.primeFactors.card =
      b.primeFactors.card + c.primeFactors.card + d.primeFactors.card := by
    have hdisjBCD : Disjoint
        (b.primeFactors ∪ c.primeFactors) d.primeFactors := by
      rw [← Nat.primeFactors_mul hb.ne' hc.ne']
      exact hsplit.1.disjoint_primeFactors
    rw [hval,
      Nat.primeFactors_mul
        (Nat.mul_ne_zero
          (pow_ne_zero _ hb.ne') (pow_ne_zero _ hc.ne'))
        (pow_ne_zero _ hd.ne'),
      Nat.primeFactors_mul (pow_ne_zero _ hb.ne') (pow_ne_zero _ hc.ne'),
      Nat.primeFactors_pow b (by norm_num : 5 ≠ 0),
      Nat.primeFactors_pow c (by norm_num : 6 ≠ 0),
      Nat.primeFactors_pow d (by norm_num : 7 ≠ 0),
      Finset.card_union_of_disjoint hdisjBCD,
      Finset.card_union_of_disjoint hbc.1.disjoint_primeFactors]
  rw [hprod, primeFactor_weight_product b hbc.2.1,
    primeFactor_weight_product c hbc.2.2,
    primeFactor_weight_product d hsplit.2.2, hcard]
  have hweight :
      (b : ℝ) ^ (-(5 * s)) *
        ((c : ℝ) ^ (-(6 * s)) * (d : ℝ) ^ (-(7 * s))) =
        (a.val : ℝ) ^ (-s) := by
    exact tripleWeightExponent_partTriple s a
  rw [pow_add, pow_add]
  rw [← hweight]
  ring

/-- A single canonical coefficient has a summable `4^ω`-weighted series
throughout the range needed for the quartic argument. -/
theorem summable_canonicalPart_weighted (s : ℝ) (hs : 1 / 5 < s) :
    Summable (fun a : CanonicalParts =>
      (4 : ℝ) ^ a.val.primeFactors.card * (a.val : ℝ) ^ (-s)) := by
  have h := (summable_primeChoiceProducts s hs).comp_injective
    coloredFactors_injective
  exact h.congr (fun a => coloredFactors_weight s a)

/-- Positive 4-powerful numbers below a cutoff. -/
noncomputable def fourFullBelow (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range N).filter FourFull

private noncomputable def canonicalOf (n : ℕ) : CanonicalData := by
  classical
  exact if h : FourFull n then Classical.choose (exists_canonicalData_of_fourFull n h)
    else ⟨1, 1, 1, 1, by decide, by decide, by decide, by decide, by simp⟩

private theorem canonicalOf_value (n : ℕ) (hn : FourFull n) :
    (canonicalOf n).value = n := by
  simp only [canonicalOf, dite_eq_left hn]
  exact Classical.choose_spec (exists_canonicalData_of_fourFull n hn)

private noncomputable def partOf (n : ℕ) : CanonicalParts :=
  ⟨(canonicalOf n).b ^ 5 * (canonicalOf n).c ^ 6 *
    (canonicalOf n).d ^ 7, (canonicalOf n).part⟩

private theorem canonicalOf_value_part (n : ℕ) (hn : FourFull n) :
    n = (canonicalOf n).x ^ 4 * (partOf n).val := by
  simpa [CanonicalData.value, partOf, mul_assoc] using (canonicalOf_value n hn).symm

private noncomputable def partFiber (N : ℕ) (a : CanonicalParts) : Finset ℕ :=
  (fourFullBelow N).filter (fun n => partOf n = a)

private theorem partFiber_card_le (N : ℕ) (a : CanonicalParts) :
    ((partFiber N a).card : ℝ) ≤
      (N : ℝ) ^ (1 / 4 : ℝ) * (a.val : ℝ) ^ (-(1 / 4 : ℝ)) := by
  classical
  let y : ℝ := ((N : ℝ) / (a.val : ℝ)) ^ (1 / 4 : ℝ)
  have hapos : 0 < (a.val : ℝ) := by
    exact_mod_cast CanonicalPart.pos a.property
  have hy : 0 ≤ y := Real.rpow_nonneg (div_nonneg (by positivity) hapos.le) _
  have hinj : Set.InjOn (fun n : ℕ => (canonicalOf n).x) (partFiber N a) := by
    intro n hn m hm hxm
    have hnn : FourFull n := (Finset.mem_filter.mp hn).1 |> Finset.mem_filter.mp |>.2
    have hnm : FourFull m := (Finset.mem_filter.mp hm).1 |> Finset.mem_filter.mp |>.2
    have hpn : partOf n = a := (Finset.mem_filter.mp hn).2
    have hpm : partOf m = a := (Finset.mem_filter.mp hm).2
    change (canonicalOf n).x = (canonicalOf m).x at hxm
    calc
      n = (canonicalOf n).x ^ 4 * (partOf n).val := canonicalOf_value_part n hnn
      _ = (canonicalOf m).x ^ 4 * (partOf m).val := by rw [hxm, hpn, hpm]
      _ = m := (canonicalOf_value_part m hnm).symm
  have hsubset : (partFiber N a).image (fun n : ℕ => (canonicalOf n).x) ⊆
      Finset.Ioc 0 (Nat.floor y) := by
    intro x hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
    have hfull : FourFull n := (Finset.mem_filter.mp hn).1 |> Finset.mem_filter.mp |>.2
    have hnlt : n < N := Finset.mem_range.mp
      ((Finset.mem_filter.mp hn).1 |> Finset.mem_filter.mp |>.1)
    have hpart : partOf n = a := (Finset.mem_filter.mp hn).2
    have hxa : (canonicalOf n).x ^ 4 * a.val ≤ N := by
      have hidentity := canonicalOf_value_part n hfull
      rw [hpart] at hidentity
      omega
    have hquot : ((canonicalOf n).x : ℝ) ^ 4 ≤
        (N : ℝ) / (a.val : ℝ) := by
      apply (le_div_iff₀ hapos).2
      exact_mod_cast hxa
    have hroot : ((canonicalOf n).x : ℝ) ≤ y := by
      have hroot' := Real.rpow_le_rpow
        (by positivity : 0 ≤ ((canonicalOf n).x : ℝ) ^ 4)
        hquot (by norm_num : (0 : ℝ) ≤ 1 / 4)
      have hsimp : (((canonicalOf n).x : ℝ) ^ 4) ^ (1 / 4 : ℝ) =
          ((canonicalOf n).x : ℝ) := by
        convert Real.pow_rpow_inv_natCast
          (by positivity : 0 ≤ ((canonicalOf n).x : ℝ))
          (by norm_num : (4 : ℕ) ≠ 0) using 1; norm_num
      exact hsimp ▸ hroot'
    exact Finset.mem_Ioc.mpr ⟨(canonicalOf n).x_pos,
      (Nat.le_floor_iff hy).2 hroot⟩
  have hcard : (partFiber N a).card ≤ Nat.floor y := by
    calc
      (partFiber N a).card =
          ((partFiber N a).image (fun n : ℕ => (canonicalOf n).x)).card :=
        (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.Ioc 0 (Nat.floor y)).card := Finset.card_le_card hsubset
      _ = Nat.floor y := by simp
  have hbound : ((partFiber N a).card : ℝ) ≤ y :=
    (Nat.cast_le.mpr hcard).trans (Nat.floor_le hy)
  calc
    ((partFiber N a).card : ℝ) ≤ y := hbound
    _ = (N : ℝ) ^ (1 / 4 : ℝ) * (a.val : ℝ) ^ (-(1 / 4 : ℝ)) := by
      dsimp only [y]
      rw [Real.div_rpow (by positivity) hapos.le]
      rw [Real.rpow_neg hapos.le]
      simp [div_eq_mul_inv]

/-- The count of positive 4-powerful numbers below `N` is `O(N^(1/4))`. -/
theorem fourFullBelow_card_le_fourthRoot :
    ∃ W : ℝ, 0 < W ∧ ∀ N : ℕ,
      ((fourFullBelow N).card : ℝ) ≤ W * (N : ℝ) ^ (1 / 4 : ℝ) := by
  let w : CanonicalParts → ℝ := fun a => (a.val : ℝ) ^ (-(1 / 4 : ℝ))
  have hw : Summable w := summable_canonicalPart_weight
  have hw0 : ∀ a, 0 ≤ w a := by intro a; positivity
  let W : ℝ := (∑' a, w a) + 1
  have hW : 0 < W := by
    have htsum : 0 ≤ ∑' a, w a := tsum_nonneg hw0
    dsimp [W]
    linarith
  refine ⟨W, hW, ?_⟩
  intro N
  let A := fourFullBelow N
  let D := A.image partOf
  have hcard : A.card = ∑ a ∈ D, (partFiber N a).card := by
    simpa only [A, D, partFiber] using Finset.card_eq_sum_card_image partOf A
  have hsum : (∑ a ∈ D, w a) ≤ ∑' a, w a :=
    hw.sum_le_tsum D (fun a ha => hw0 a)
  have hN0 : 0 ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by positivity
  calc
    ((fourFullBelow N).card : ℝ) =
        ∑ a ∈ D, ((partFiber N a).card : ℝ) := by exact_mod_cast hcard
    _ ≤ ∑ a ∈ D, (N : ℝ) ^ (1 / 4 : ℝ) * w a := by
      apply Finset.sum_le_sum
      intro a ha
      exact partFiber_card_le N a
    _ = (N : ℝ) ^ (1 / 4 : ℝ) * (∑ a ∈ D, w a) := by
      rw [Finset.mul_sum]
    _ ≤ (N : ℝ) ^ (1 / 4 : ℝ) * (∑' a, w a) :=
      mul_le_mul_of_nonneg_left hsum hN0
    _ ≤ W * (N : ℝ) ^ (1 / 4 : ℝ) := by
      dsimp only [W]
      nlinarith

/-- Values of sums of at most three positive 4-powerful numbers below `N`.
The zero-summand value is included. -/
noncomputable def atMostThreeSumsBelow (N : ℕ) : Finset ℕ := by
  classical
  let A := fourFullBelow N
  let B := Finset.image₂ (· + ·) A A
  let C := Finset.image₂ (· + ·) B A
  exact insert 0 (A ∪ B ∪ C)

theorem atMostThreeSumsBelow_card_le (N : ℕ) :
    (atMostThreeSumsBelow N).card ≤
      1 + (fourFullBelow N).card + (fourFullBelow N).card ^ 2 +
        (fourFullBelow N).card ^ 3 := by
  classical
  let A := fourFullBelow N
  let B := Finset.image₂ (· + ·) A A
  let C := Finset.image₂ (· + ·) B A
  have hB : B.card ≤ A.card ^ 2 := by
    simpa only [pow_two] using Finset.card_image₂_le (· + ·) A A
  have hC : C.card ≤ A.card ^ 3 := by
    calc
      C.card ≤ B.card * A.card := Finset.card_image₂_le (· + ·) B A
      _ ≤ A.card ^ 2 * A.card := Nat.mul_le_mul_right A.card hB
      _ = A.card ^ 3 := by ring
  change (insert 0 (A ∪ B ∪ C)).card ≤ 1 + A.card + A.card ^ 2 + A.card ^ 3
  calc
    (insert 0 (A ∪ B ∪ C)).card ≤ 1 + (A ∪ B ∪ C).card := by
      simpa only [add_comm] using Finset.card_insert_le 0 (A ∪ B ∪ C)
    _ ≤ 1 + (A ∪ B).card + C.card := by
      simpa only [add_assoc] using
        Nat.add_le_add_left (Finset.card_union_le (A ∪ B) C) 1
    _ ≤ 1 + (A.card + B.card) + C.card := by
      exact Nat.add_le_add_right
        (Nat.add_le_add_left (Finset.card_union_le _ _) 1) C.card
    _ ≤ 1 + A.card + A.card ^ 2 + A.card ^ 3 := by omega

/-- Sums of at most three positive 4-powerful numbers have sublinear count. -/
theorem atMostThreeSumsBelow_eventually_small (C : ℕ) :
    ∀ᶠ N in Filter.atTop, C * (atMostThreeSumsBelow N).card ≤ N := by
  obtain ⟨W, hW, hcount⟩ := fourFullBelow_card_le_fourthRoot
  let K : ℝ := 1 + W + W ^ 2 + W ^ 3
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have htend : Filter.Tendsto
      (fun N : ℕ => (N : ℝ) ^ (1 / 4 : ℝ)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [htend.eventually_ge_atTop ((C : ℝ) * K + 1),
    Filter.eventually_gt_atTop 0] with N hroot hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  let q : ℝ := (N : ℝ) ^ (1 / 4 : ℝ)
  have hq1 : 1 ≤ q := by
    dsimp [q]
    exact Real.one_le_rpow hN1 (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hq0 : 0 ≤ q := le_trans (by norm_num) hq1
  have hq4 : q ^ 4 = (N : ℝ) := by
    dsimp [q]
    rw [← Real.rpow_mul_natCast (by positivity : 0 ≤ (N : ℝ)) (1 / 4 : ℝ) 4]
    norm_num
  have hcard : ((atMostThreeSumsBelow N).card : ℝ) ≤ K * q ^ 3 := by
    have hA := hcount N
    have hAr : 0 ≤ ((fourFullBelow N).card : ℝ) := by positivity
    have hA3 : ((fourFullBelow N).card : ℝ) ^ 3 ≤ (W * q) ^ 3 :=
      pow_le_pow_left₀ hAr hA 3
    have hA2 : ((fourFullBelow N).card : ℝ) ^ 2 ≤ (W * q) ^ 2 :=
      pow_le_pow_left₀ hAr hA 2
    have hraw : ((atMostThreeSumsBelow N).card : ℝ) ≤
        1 + ((fourFullBelow N).card : ℝ) +
          ((fourFullBelow N).card : ℝ) ^ 2 +
          ((fourFullBelow N).card : ℝ) ^ 3 := by
      exact_mod_cast atMostThreeSumsBelow_card_le N
    have hq2 : q ^ 2 ≤ q ^ 3 := by nlinarith [sq_nonneg q]
    have hq3 : 1 ≤ q ^ 3 := by nlinarith [sq_nonneg q]
    dsimp [K]
    nlinarith [sq_nonneg W, pow_nonneg hq0 3]
  have hsmall : ((C * (atMostThreeSumsBelow N).card : ℕ) : ℝ) ≤ (N : ℝ) := by
    calc
      ((C * (atMostThreeSumsBelow N).card : ℕ) : ℝ) =
          (C : ℝ) * ((atMostThreeSumsBelow N).card : ℝ) := by norm_num
      _ ≤ (C : ℝ) * (K * q ^ 3) :=
        mul_le_mul_of_nonneg_left hcard (by positivity)
      _ ≤ q ^ 4 := by nlinarith [pow_nonneg hq0 3]
      _ = N := hq4
  exact_mod_cast hsmall

end Erdos940.Quartic
