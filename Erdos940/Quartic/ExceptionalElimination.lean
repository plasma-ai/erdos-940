import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Erdos940.Quartic.CanonicalParts
import Erdos940.Quartic.HilbertBridge
import Erdos940.Quartic.LocalQuartic
import Erdos940.Quartic.LocalPerturbationCongruence
import Erdos940.Quartic.QuadraticZeroCount
import Erdos940.Quartic.QuarticHenselLift
import Erdos940.Quartic.QuadraticHenselLift
import Erdos940.Quartic.RationalQuadraticHenselLift
import Erdos940.Quartic.LocalCRT

open scoped NumberField
open NumberField IsDedekindDomain

/-!
# Algebraic reduction of exceptional quartic forms

The second exceptional family in the quartic complement proof is defined by a
fourth-power condition on a permutation of the coefficients.  Its quartic form
maps to a positive quaternary quadratic form with square determinant.  This
algebraic reduction rules out a nonzero base point; finite-place isotropy and
Hilbert reciprocity rule out the corresponding global configuration.
-/

namespace Erdos940.Quartic

/-- A version of the mixed exceptional condition with an explicit rational
fourth root.  The witness is allowed to be rational, as in the paper. -/
def MixedExceptional (a b c d : ℚ) : Prop :=
  ∃ r : ℚ, a * b ^ 3 * c ^ 2 * d ^ 2 = 4 * r ^ 4

/-- The rational square ratio dictated by the exceptional condition. -/
noncomputable def mixedRatio (a b c d r : ℚ) : ℚ :=
  2 * r ^ 2 / (a * b * c * d)

theorem mixedRatio_sq
    (a b c d r : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (h : a * b ^ 3 * c ^ 2 * d ^ 2 = 4 * r ^ 4) :
    b = a * (mixedRatio a b c d r) ^ 2 := by
  unfold mixedRatio
  field_simp
  linear_combination h

/-- The mixed fourth-power condition implies that the product of the two
paired positive integer coefficients is an integer square. -/
theorem mixedExceptional_nat_paired_product_square
    (a b c d : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : MixedExceptional (a : ℚ) (b : ℚ) (c : ℚ) (d : ℚ)) :
    IsSquare (a * b) := by
  obtain ⟨r, hr⟩ := h
  have hratio := mixedRatio_sq (a : ℚ) (b : ℚ) (c : ℚ) (d : ℚ) r
    (by exact_mod_cast ha.ne') (by exact_mod_cast hb.ne')
    (by exact_mod_cast hc.ne') (by exact_mod_cast hd.ne') hr
  apply Rat.isSquare_natCast_iff.mp
  refine ⟨(a : ℚ) * mixedRatio a b c d r, ?_⟩
  calc
    ((a * b : ℕ) : ℚ) = (a : ℚ) * (b : ℚ) := by norm_cast
    _ = (a : ℚ) * ((a : ℚ) * (mixedRatio a b c d r) ^ 2) :=
      congrArg ((a : ℚ) * ·) hratio
    _ = ((a : ℚ) * mixedRatio a b c d r) *
        ((a : ℚ) * mixedRatio a b c d r) := by ring

/-- The map used for the mixed exceptional family has no nonzero base point. -/
theorem mixedQuartic_map_zero
    {K : Type*} [Field K] (t x y z w : K) (ht : t ≠ 0)
    (h₁ : x ^ 2 - t * y ^ 2 = 0) (h₂ : z ^ 2 = 0)
    (h₃ : w ^ 2 = 0) (h₄ : x * y = 0) :
    x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0 := by
  have hz : z = 0 := mul_self_eq_zero.mp (by simpa [pow_two] using h₂)
  have hw : w = 0 := mul_self_eq_zero.mp (by simpa [pow_two] using h₃)
  rcases mul_eq_zero.mp h₄ with hx | hy
  · have hy2 : y ^ 2 = 0 := by simpa [hx, ht] using h₁
    exact ⟨hx, mul_self_eq_zero.mp (by simpa [pow_two] using hy2), hz, hw⟩
  · have hx2 : x ^ 2 = 0 := by simpa [hy] using h₁
    exact ⟨mul_self_eq_zero.mp (by simpa [pow_two] using hx2), hy, hz, hw⟩

/-- The quartic-to-quadratic identity; it is valid over every commutative ring. -/
theorem mixedQuartic_quadratic_identity
    {K : Type*} [CommRing K] (a b c d t x y z w : K)
    (hb : b = a * t ^ 2) :
    a * x ^ 4 + b * y ^ 4 + c * z ^ 4 + d * w ^ 4 =
      a * (x ^ 2 - t * y ^ 2) ^ 2 +
        c * (z ^ 2) ^ 2 + d * (w ^ 2) ^ 2 +
        (2 * a * t) * (x * y) ^ 2 := by
  rw [hb]
  ring

/-- The fourth-power condition supplies a square-determinant quaternary
quadratic form.  Here the first coefficient itself plays the role of `A`;
the squarefree presentation of `A` is not needed for this algebraic step. -/
theorem mixedExceptional_square_determinant
    (a b c d : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (h : MixedExceptional a b c d) :
    ∃ t k : ℚ, t ≠ 0 ∧ b = a * t ^ 2 ∧
      a * c * d * (2 * a * t) = k ^ 2 := by
  obtain ⟨r, hr⟩ := h
  let t := mixedRatio a b c d r
  have hratio : b = a * t ^ 2 := mixedRatio_sq a b c d r ha hb hc hd hr
  have ht : t ≠ 0 := by
    intro hzero
    apply hb
    simpa [hzero] using hratio
  have hprod : a * b * c * d ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero ha hb) hc) hd
  have htdef : t * (a * b * c * d) = 2 * r ^ 2 := by
    dsimp [t, mixedRatio]
    exact div_mul_cancel₀ _ hprod
  have hmul : (a * c * d * (2 * a * t)) * t ^ 2 = 4 * r ^ 2 := by
    calc
      (a * c * d * (2 * a * t)) * t ^ 2 = 2 * t * (a * b * c * d) := by
        rw [hratio]
        ring
      _ = 4 * r ^ 2 := by linear_combination 2 * htdef
  refine ⟨t, 2 * r / t, ht, hratio, ?_⟩
  rw [div_pow]
  apply (eq_div_iff (pow_ne_zero 2 ht)).2
  convert hmul using 1; ring

/-- For positive coefficients the quadratic form obtained from the mixed
exceptional condition is positive definite as well as square-determinant. -/
theorem mixedExceptional_positive_quadratic
    (a b c d : ℚ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : MixedExceptional a b c d) :
    ∃ t k : ℚ, 0 < t ∧ 0 < 2 * a * t ∧ b = a * t ^ 2 ∧
      a * c * d * (2 * a * t) = k ^ 2 := by
  obtain ⟨t, k, ht, hratio, hdet⟩ :=
    mixedExceptional_square_determinant a b c d ha.ne' hb.ne' hc.ne' hd.ne' h
  have hprod : 0 < a * c * d := mul_pos (mul_pos ha hc) hd
  have htpos : 0 < t := by
    rcases lt_trichotomy t 0 with hneg | hzero | hpos
    · have hcoef : 2 * a * t < 0 :=
        mul_neg_of_pos_of_neg (mul_pos (by norm_num) ha) hneg
      have hdetneg : a * c * d * (2 * a * t) < 0 :=
        mul_neg_of_pos_of_neg hprod hcoef
      rw [hdet] at hdetneg
      exact (not_lt_of_ge (sq_nonneg k) hdetneg).elim
    · exact (ht hzero).elim
    · exact hpos
  refine ⟨t, k, htpos, ?_, hratio, hdet⟩
  exact mul_pos (mul_pos (by norm_num) ha) htpos

/-- A nonzero zero of the mixed exceptional quartic maps to a nonzero zero
of the associated square-determinant quadratic form. -/
theorem mixedQuartic_isotropic_forward
    {K : Type*} [Field K] (a b c d t x y z w : K)
    (ht : t ≠ 0) (hb : b = a * t ^ 2)
    (hnonzero : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 ∨ w ≠ 0)
    (hzero : a * x ^ 4 + b * y ^ 4 + c * z ^ 4 + d * w ^ 4 = 0) :
    ∃ U V W Z : K,
      (U ≠ 0 ∨ V ≠ 0 ∨ W ≠ 0 ∨ Z ≠ 0) ∧
      a * U ^ 2 + c * V ^ 2 + d * W ^ 2 + (2 * a * t) * Z ^ 2 = 0 := by
  refine ⟨x ^ 2 - t * y ^ 2, z ^ 2, w ^ 2, x * y, ?_, ?_⟩
  · by_contra h
    simp only [not_or, not_not] at h
    obtain ⟨hx, hy, hz, hw⟩ :=
      mixedQuartic_map_zero t x y z w ht h.1 h.2.1 h.2.2.1 h.2.2.2
    simp [hx, hy, hz, hw] at hnonzero
  · rw [mixedQuartic_quadratic_identity a b c d t x y z w hb] at hzero
    exact hzero

/-- At odd residue characteristic, a nonzero summand of a zero of the mixed
quartic supplies a nonzero summand of the associated quadratic form.  If
neither unchanged term survives, both paired terms must survive and then the
cross term does. -/
theorem mixedQuartic_nonzero_quadratic_term
    {K : Type*} [Field K] (a b c d t x y z w : K)
    (h2 : (2 : K) ≠ 0) (hb : b = a * t ^ 2)
    (hzero : a * x ^ 4 + b * y ^ 4 + c * z ^ 4 + d * w ^ 4 = 0)
    (hunit : a * x ^ 4 ≠ 0 ∨ b * y ^ 4 ≠ 0 ∨
      c * z ^ 4 ≠ 0 ∨ d * w ^ 4 ≠ 0) :
    c * z ^ 4 ≠ 0 ∨ d * w ^ 4 ≠ 0 ∨ (2 * a * t) * (x * y) ^ 2 ≠ 0 := by
  by_cases hcz : c * z ^ 4 ≠ 0
  · exact Or.inl hcz
  by_cases hdw : d * w ^ 4 ≠ 0
  · exact Or.inr (Or.inl hdw)
  have hpair : a * x ^ 4 + b * y ^ 4 = 0 := by
    simpa [not_not.mp hcz, not_not.mp hdw] using hzero
  have hax : a * x ^ 4 ≠ 0 := by
    rcases hunit with hax | hby | hcz' | hdw'
    · exact hax
    · intro hax0
      have hby0 : b * y ^ 4 = 0 := by simpa [hax0] using hpair
      exact hby hby0
    · exact (hcz hcz').elim
    · exact (hdw hdw').elim
  have hby : b * y ^ 4 ≠ 0 := by
    intro hby0
    exact hax (by simpa [hby0] using hpair)
  have ha : a ≠ 0 := (mul_ne_zero_iff.mp hax).1
  have hb0 : b ≠ 0 := (mul_ne_zero_iff.mp hby).1
  have hx : x ≠ 0 := by
    intro hx0
    exact hax (by simp [hx0])
  have hy : y ≠ 0 := by
    intro hy0
    exact hby (by simp [hy0])
  have ht : t ≠ 0 := by
    intro ht0
    exact hb0 (by simp [hb, ht0])
  exact Or.inr (Or.inr
    (mul_ne_zero (mul_ne_zero (mul_ne_zero h2 ha) ht)
      (pow_ne_zero 2 (mul_ne_zero hx hy))))

/-- In the square-determinant family, squaring coordinates maps a nonzero
quartic zero to a nonzero zero of the diagonal quadratic form. -/
theorem squareExceptional_isotropic_forward
    {K : Type*} [Field K] (a b c d x y z w : K)
    (hnonzero : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 ∨ w ≠ 0)
    (hzero : a * x ^ 4 + b * y ^ 4 + c * z ^ 4 + d * w ^ 4 = 0) :
    ∃ U V W Z : K,
      (U ≠ 0 ∨ V ≠ 0 ∨ W ≠ 0 ∨ Z ≠ 0) ∧
      a * U ^ 2 + b * V ^ 2 + c * W ^ 2 + d * Z ^ 2 = 0 := by
  refine ⟨x ^ 2, y ^ 2, z ^ 2, w ^ 2, ?_, ?_⟩
  · rcases hnonzero with hx | hy | hz | hw
    · exact Or.inl (pow_ne_zero 2 hx)
    · exact Or.inr (Or.inl (pow_ne_zero 2 hy))
    · exact Or.inr (Or.inr (Or.inl (pow_ne_zero 2 hz)))
    · exact Or.inr (Or.inr (Or.inr (pow_ne_zero 2 hw)))
  · convert hzero using 1; ring

/-- Hilbert reciprocity excludes a nonzero quartic zero at some finite place
for a positive square-determinant coefficient tuple. -/
theorem exists_finite_squareExceptional_quartic_anisotropic
    (a b c d k : ℚ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hk : k ^ 2 = a * b * c * d) :
    ∃ v : HeightOneSpectrum (𝓞 ℚ),
      ∀ x y z w : v.adicCompletion ℚ,
        (a : v.adicCompletion ℚ) * x ^ 4 + (b : v.adicCompletion ℚ) * y ^ 4 +
          (c : v.adicCompletion ℚ) * z ^ 4 + (d : v.adicCompletion ℚ) * w ^ 4 = 0 →
        x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0 := by
  obtain ⟨v, hv⟩ :=
    exists_finite_anisotropic_positive_square_det_diagonal a b c d k ha hb hc hd hk
  refine ⟨v, ?_⟩
  intro x y z w hzero
  by_contra hnon
  have hnon' : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 ∨ w ≠ 0 := by
    simpa only [not_and_or] using hnon
  obtain ⟨U, V, W, Z, hNZ, hQ⟩ :=
    squareExceptional_isotropic_forward
      (a : v.adicCompletion ℚ) (b : v.adicCompletion ℚ)
      (c : v.adicCompletion ℚ) (d : v.adicCompletion ℚ)
      x y z w hnon' hzero
  obtain ⟨hU, hV, hW, hZ⟩ := hv U V W Z hQ
  simp [hU, hV, hW, hZ] at hNZ

/-- The mixed exceptional family has a finite place where its quartic form
has no nonzero zero.  The quadratic form is obtained by the algebraic map
above and has positive coefficients and square determinant. -/
theorem exists_finite_mixedExceptional_quartic_anisotropic
    (a b c d : ℚ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : MixedExceptional a b c d) :
    ∃ v : HeightOneSpectrum (𝓞 ℚ),
      ∀ x y z w : v.adicCompletion ℚ,
        (a : v.adicCompletion ℚ) * x ^ 4 + (b : v.adicCompletion ℚ) * y ^ 4 +
          (c : v.adicCompletion ℚ) * z ^ 4 + (d : v.adicCompletion ℚ) * w ^ 4 = 0 →
        x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0 := by
  obtain ⟨t, k, ht, hcoef, hratio, hdet⟩ :=
    mixedExceptional_positive_quadratic a b c d ha hb hc hd h
  obtain ⟨v, hv⟩ :=
    exists_finite_anisotropic_positive_square_det_diagonal
      a c d (2 * a * t) k ha hc hd hcoef hdet.symm
  refine ⟨v, ?_⟩
  intro x y z w hzero
  by_contra hnon
  have hnon' : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 ∨ w ≠ 0 := by
    simpa only [not_and_or] using hnon
  have ht' : (t : v.adicCompletion ℚ) ≠ 0 := by exact_mod_cast ht.ne'
  have hratio' : (b : v.adicCompletion ℚ) =
      (a : v.adicCompletion ℚ) * (t : v.adicCompletion ℚ) ^ 2 := by
    exact_mod_cast hratio
  obtain ⟨U, V, W, Z, hNZ, hQ⟩ :=
    mixedQuartic_isotropic_forward
      (a : v.adicCompletion ℚ) (b : v.adicCompletion ℚ)
      (c : v.adicCompletion ℚ) (d : v.adicCompletion ℚ)
      (t : v.adicCompletion ℚ) x y z w ht' hratio' hnon' hzero
  have hQ' : (a : v.adicCompletion ℚ) * U ^ 2 +
      (c : v.adicCompletion ℚ) * V ^ 2 +
      (d : v.adicCompletion ℚ) * W ^ 2 +
      ((2 * a * t : ℚ) : v.adicCompletion ℚ) * Z ^ 2 = 0 := by
    convert hQ using 1; norm_num
  obtain ⟨hU, hV, hW, hZ⟩ := hv U V W Z hQ'
  simp [hU, hV, hW, hZ] at hNZ

/-- The two exceptional algebraic alternatives used by the quartic proof,
with the coefficient order fixed. -/
def ExceptionalCoefficients (a b c d : ℚ) : Prop :=
  (∃ k : ℚ, k ^ 2 = a * b * c * d) ∨ MixedExceptional a b c d

/-- An exceptional positive quartic form is anisotropic at a finite rational
place.  The prescribed congruence target must therefore be shown to force
local isotropy there, which is a separate arithmetic step. -/
theorem exceptional_has_finite_anisotropic_place
    (a b c d : ℚ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : ExceptionalCoefficients a b c d) :
    ∃ v : HeightOneSpectrum (𝓞 ℚ),
      ∀ x y z w : v.adicCompletion ℚ,
        (a : v.adicCompletion ℚ) * x ^ 4 + (b : v.adicCompletion ℚ) * y ^ 4 +
          (c : v.adicCompletion ℚ) * z ^ 4 + (d : v.adicCompletion ℚ) * w ^ 4 = 0 →
        x = 0 ∧ y = 0 ∧ z = 0 ∧ w = 0 := by
  rcases h with ⟨k, hk⟩ | hm
  · exact exists_finite_squareExceptional_quartic_anisotropic
      a b c d k ha hb hc hd hk
  · exact exists_finite_mixedExceptional_quartic_anisotropic
      a b c d ha hb hc hd hm

/-- Permutation-invariant exceptional condition for four canonical
coefficients.  The mixed alternative must hold in *some* ordering. -/
def ExceptionalTuple (d : Fin 4 → CanonicalParts) : Prop :=
  (∃ k : ℚ, k ^ 2 = ∏ i : Fin 4, ((d i).val : ℚ)) ∨
  ∃ σ : Equiv.Perm (Fin 4),
    MixedExceptional ((d (σ 0)).val : ℚ) ((d (σ 1)).val : ℚ)
      ((d (σ 2)).val : ℚ) ((d (σ 3)).val : ℚ)

private theorem canonical_coefficient_pos (d : Fin 4 → CanonicalParts) (i : Fin 4) :
    (0 : ℚ) < ((d i).val : ℚ) := by
  exact_mod_cast (d i).property.pos

/-- An exceptional canonical coefficient tuple has a finite place where its
quartic form is anisotropic, independently of the order of its summands. -/
theorem exceptionalTuple_has_finite_anisotropic_place
    (d : Fin 4 → CanonicalParts) (h : ExceptionalTuple d) :
    ∃ v : HeightOneSpectrum (𝓞 ℚ),
      ∀ x : Fin 4 → v.adicCompletion ℚ,
        (∑ i : Fin 4, ((d i).val : v.adicCompletion ℚ) * (x i) ^ 4) = 0 →
        ∀ i : Fin 4, x i = 0 := by
  rcases h with ⟨k, hk⟩ | ⟨σ, hm⟩
  · have hk' : k ^ 2 = ((d 0).val : ℚ) * ((d 1).val : ℚ) *
        ((d 2).val : ℚ) * ((d 3).val : ℚ) := by
      simpa only [Fin.prod_univ_four] using hk
    obtain ⟨v, hv⟩ := exists_finite_squareExceptional_quartic_anisotropic
      ((d 0).val : ℚ) ((d 1).val : ℚ) ((d 2).val : ℚ) ((d 3).val : ℚ) k
      (canonical_coefficient_pos d 0) (canonical_coefficient_pos d 1)
      (canonical_coefficient_pos d 2) (canonical_coefficient_pos d 3) hk'
    refine ⟨v, ?_⟩
    intro x hzero i
    have hfour : ((d 0).val : v.adicCompletion ℚ) * (x 0) ^ 4 +
        ((d 1).val : v.adicCompletion ℚ) * (x 1) ^ 4 +
        ((d 2).val : v.adicCompletion ℚ) * (x 2) ^ 4 +
        ((d 3).val : v.adicCompletion ℚ) * (x 3) ^ 4 = 0 := by
      simpa only [Fin.sum_univ_four] using hzero
    have hfour' := hv (x 0) (x 1) (x 2) (x 3)
      (by exact_mod_cast hfour)
    obtain ⟨h0, h1, h2, h3⟩ := hfour'
    fin_cases i <;> assumption
  · obtain ⟨v, hv⟩ := exists_finite_mixedExceptional_quartic_anisotropic
      ((d (σ 0)).val : ℚ) ((d (σ 1)).val : ℚ)
      ((d (σ 2)).val : ℚ) ((d (σ 3)).val : ℚ)
      (canonical_coefficient_pos d (σ 0)) (canonical_coefficient_pos d (σ 1))
      (canonical_coefficient_pos d (σ 2)) (canonical_coefficient_pos d (σ 3)) hm
    refine ⟨v, ?_⟩
    intro x hzero i
    have hperm : (∑ j : Fin 4,
        ((d (σ j)).val : v.adicCompletion ℚ) * (x (σ j)) ^ 4) = 0 := by
      exact (Fintype.sum_equiv σ
        (fun j : Fin 4 => ((d (σ j)).val : v.adicCompletion ℚ) * (x (σ j)) ^ 4)
        (fun j : Fin 4 => ((d j).val : v.adicCompletion ℚ) * (x j) ^ 4)
        (by intro j; rfl)).trans hzero
    have hfour : ((d (σ 0)).val : v.adicCompletion ℚ) * (x (σ 0)) ^ 4 +
        ((d (σ 1)).val : v.adicCompletion ℚ) * (x (σ 1)) ^ 4 +
        ((d (σ 2)).val : v.adicCompletion ℚ) * (x (σ 2)) ^ 4 +
        ((d (σ 3)).val : v.adicCompletion ℚ) * (x (σ 3)) ^ 4 = 0 := by
      simpa only [Fin.sum_univ_four] using hperm
    have hfour' := hv (x (σ 0)) (x (σ 1)) (x (σ 2)) (x (σ 3))
      (by exact_mod_cast hfour)
    obtain ⟨h0, h1, h2, h3⟩ := hfour'
    obtain ⟨j, rfl⟩ := σ.surjective i
    fin_cases j <;> assumption

/-- At an odd prime not dividing the canonical coefficients, the associated
diagonal quadratic form already has a nonzero zero over the residue field.
The separate perturbation step lifts this zero to the finite completion. -/
theorem canonicalTuple_quadratic_zero_mod_good_prime
    (d : Fin 4 → CanonicalParts) (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2)
    (hgood : ∀ i : Fin 4, ¬ p ∣ (d i).val) :
    ∃ x : Fin 4 → ZMod p,
      (∑ i : Fin 4, ((d i).val : ZMod p) * (x i) ^ 2) = 0 ∧ x ≠ 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  apply zmod_quadratic_four_nontrivial_zero hodd
  intro i hzero
  exact hgood i ((ZMod.natCast_eq_zero_iff _ _).mp hzero)

/-- A prime dividing a canonical quartic coefficient appears with exponent
at least five, and hence already annihilates that coefficient modulo `p²`. -/
theorem canonicalPart_prime_square_dvd (a : CanonicalParts) (p : ℕ)
    (hp : p.Prime) (hpa : p ∣ a.val) : p ^ 2 ∣ a.val := by
  obtain ⟨b, c, d, _, _, _, _, ha⟩ := a.property
  rw [ha] at hpa ⊢
  rcases hp.dvd_mul.mp hpa with hbc | hd
  · rcases hp.dvd_mul.mp hbc with hb | hc
    · have hpb : p ∣ b := hp.dvd_of_dvd_pow hb
      have hp2 : p ^ 2 ∣ b ^ 5 :=
        pow_dvd_pow_of_dvd_of_le hpb (by decide : 2 ≤ 5)
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hp2 _) _
    · have hpc : p ∣ c := hp.dvd_of_dvd_pow hc
      have hp2 : p ^ 2 ∣ c ^ 6 :=
        pow_dvd_pow_of_dvd_of_le hpc (by decide : 2 ≤ 6)
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hp2 _) _
  · have hpd : p ∣ d := hp.dvd_of_dvd_pow hd
    have hp2 : p ^ 2 ∣ d ^ 7 :=
      pow_dvd_pow_of_dvd_of_le hpd (by decide : 2 ≤ 7)
    exact dvd_mul_of_dvd_right hp2 _

/-- The stronger divisibility needed at the prime two. -/
theorem canonicalPart_prime_fourth_dvd (a : CanonicalParts) (p : ℕ)
    (hp : p.Prime) (hpa : p ∣ a.val) : p ^ 4 ∣ a.val := by
  obtain ⟨b, c, d, _, _, _, _, ha⟩ := a.property
  rw [ha] at hpa ⊢
  rcases hp.dvd_mul.mp hpa with hbc | hd
  · rcases hp.dvd_mul.mp hbc with hb | hc
    · have hpb : p ∣ b := hp.dvd_of_dvd_pow hb
      have hp4 : p ^ 4 ∣ b ^ 5 :=
        pow_dvd_pow_of_dvd_of_le hpb (by decide : 4 ≤ 5)
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hp4 _) _
    · have hpc : p ∣ c := hp.dvd_of_dvd_pow hc
      have hp4 : p ^ 4 ∣ c ^ 6 :=
        pow_dvd_pow_of_dvd_of_le hpc (by decide : 4 ≤ 6)
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hp4 _) _
  · have hpd : p ∣ d := hp.dvd_of_dvd_pow hd
    have hp4 : p ^ 4 ∣ d ^ 7 :=
      pow_dvd_pow_of_dvd_of_le hpd (by decide : 4 ≤ 7)
    exact dvd_mul_of_dvd_right hp4 _

/-- A valuation-one target modulo `p²` forces one nonsingular coordinate
among canonical coefficients. -/
theorem canonicalTuple_unit_coordinate_of_target
    (d : Fin 4 → CanonicalParts) (p : ℕ) (hp : p.Prime)
    (x : Fin 4 → ZMod (p ^ 2))
    (hsol : (∑ i : Fin 4, ((d i).val : ZMod (p ^ 2)) * (x i) ^ 4) =
      (p : ZMod (p ^ 2))) :
    ∃ i : Fin 4, ((d i).val : ZMod p) ≠ 0 ∧
      (ZMod.cast (x i) : ZMod p) ≠ 0 := by
  apply zmod_prime_square_quartic_unit_coordinate_nat p hp (fun i => (d i).val) x
  · intro i hpi
    exact canonicalPart_prime_square_dvd (d i) p hp hpi
  · exact hsol

/-- The valuation-one target also forces an integral unit coordinate before
passing to any local completion. -/
theorem canonicalTuple_nat_unit_coordinate_of_target
    (d : Fin 4 → CanonicalParts) (p : ℕ) (hp : p.Prime)
    (x : Fin 4 → ℕ)
    (hsol : (∑ i : Fin 4, (d i).val * x i ^ 4) % (p ^ 2) = p) :
    ∃ i : Fin 4, ¬p ∣ (d i).val ∧ ¬p ∣ x i := by
  have hlt : p < p ^ 2 := by
    have hp2 := hp.two_le
    nlinarith
  have hsolZ :
      (∑ i : Fin 4, ((d i).val : ZMod (p ^ 2)) *
        (x i : ZMod (p ^ 2)) ^ 4) = (p : ZMod (p ^ 2)) := by
    have hs : ((∑ i : Fin 4, (d i).val * x i ^ 4 : ℕ) : ZMod (p ^ 2)) =
        (p : ZMod (p ^ 2)) := by
      apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
      simpa [Nat.mod_eq_of_lt hlt] using hsol
    simpa only [Nat.cast_sum, Nat.cast_mul, Nat.cast_pow] using hs
  obtain ⟨i, hdi, hxi⟩ :=
    canonicalTuple_unit_coordinate_of_target d p hp
      (fun i => (x i : ZMod (p ^ 2))) hsolZ
  refine ⟨i, ?_, ?_⟩
  · intro hd
    exact hdi ((ZMod.natCast_eq_zero_iff _ _).mpr hd)
  · intro hx
    apply hxi
    rw [ZMod.cast_natCast (show p ∣ p ^ 2 by simp)]
    exact (ZMod.natCast_eq_zero_iff _ _).mpr hx

/-- An integer diagonal quadratic value divisible by the local prime (or by
eight at the dyadic place) becomes a nonzero local zero when one represented
term is a unit.  This packages the congruence-to-smallness and perturbation
lemmas for later use with the exceptional forms. -/
theorem finiteCompletion_integer_diagonal_zero_of_unit
    (place : HeightOneSpectrum (𝓞 ℚ)) (a z : Fin 4 → ℕ)
    (i : Fin 4) (N : ℕ)
    (hvalue : (∑ j : Fin 4, a j * z j ^ 2) = N)
    (hunit : ¬(finitePlacePadicPrime place : ℕ) ∣ a i * z i ^ 2)
    (hdiv : ((finitePlacePadicPrime place : ℕ) ≠ 2 ∧
        (finitePlacePadicPrime place : ℕ) ∣ N) ∨
      ((finitePlacePadicPrime place : ℕ) = 2 ∧ 8 ∣ N)) :
    ∃ z' : Fin 4 → place.adicCompletion ℚ,
      z' i ≠ 0 ∧
        (∑ j : Fin 4,
          (a j : place.adicCompletion ℚ) * z' j ^ 2) = 0 := by
  have htermCast (j : Fin 4) :
      ((a j * z j ^ 2 : ℕ) : place.adicCompletion ℚ) =
        (a j : place.adicCompletion ℚ) * (z j : place.adicCompletion ℚ) ^ 2 := by
    simp only [Nat.cast_mul, Nat.cast_pow]
  have hvalueK : (∑ j : Fin 4, (a j : place.adicCompletion ℚ) *
      (z j : place.adicCompletion ℚ) ^ 2) = (N : place.adicCompletion ℚ) := by
    calc
      (∑ j : Fin 4, (a j : place.adicCompletion ℚ) *
          (z j : place.adicCompletion ℚ) ^ 2) =
          ∑ j : Fin 4, ((a j * z j ^ 2 : ℕ) : place.adicCompletion ℚ) := by
        apply Finset.sum_congr rfl
        intro j _
        exact (htermCast j).symm
      _ = ((∑ j : Fin 4, a j * z j ^ 2 : ℕ) : place.adicCompletion ℚ) := by simp
      _ = (N : place.adicCompletion ℚ) :=
        congrArg (fun n : ℕ => (n : place.adicCompletion ℚ)) hvalue
  have hU0 : a i * z i ^ 2 ≠ 0 := by
    intro hzero
    exact hunit (by simp [hzero])
  have hterm : (a i : place.adicCompletion ℚ) *
      (z i : place.adicCompletion ℚ) ^ 2 ≠ 0 := by
    have hcast : ((a i * z i ^ 2 : ℕ) : place.adicCompletion ℚ) ≠ 0 := by
      exact_mod_cast hU0
    rw [htermCast i] at hcast
    exact hcast
  have hsmall : finiteCompletionPerturbationSmall place
      ((N : place.adicCompletion ℚ) /
        ((a i * z i ^ 2 : ℕ) : place.adicCompletion ℚ)) := by
    rcases hdiv with ⟨hodd, hN⟩ | ⟨hdyadic, hN⟩
    · exact finiteCompletion_small_of_odd_nat_dvd_unit
        place N (a i * z i ^ 2) hodd hN hunit
    · exact finiteCompletion_small_of_dyadic_nat_dvd_unit
        place N (a i * z i ^ 2) hdyadic hN hunit
  exact finiteCompletion_diagonal_quadratic_perturb_fin4 place
    (fun j => (a j : place.adicCompletion ℚ))
    (fun j => (z j : place.adicCompletion ℚ)) i
    (N : place.adicCompletion ℚ)
    hvalueK hterm (by rw [← htermCast i]; exact hsmall)

/-- Fourth powers are the parity indicator modulo 16. -/
theorem fourthPower_mod_sixteen (x : ℕ) : x ^ 4 % 16 = x % 2 := by
  have hp := (Nat.mod_modEq x 16).pow 4
  have hr : x % 16 < 16 := Nat.mod_lt x (by omega)
  interval_cases hx : x % 16 <;>
    norm_num [Nat.ModEq, hx] at hp <;>
    omega

/-- Odd squares are 1 modulo 8. -/
theorem oddSquare_mod_eight (s : ℕ) (hs : s % 2 = 1) : s ^ 2 % 8 = 1 := by
  have hp := (Nat.mod_modEq s 8).pow 2
  have hr : s % 8 < 8 := Nat.mod_lt s (by omega)
  interval_cases hres : s % 8 <;>
    norm_num [Nat.ModEq, hres] at hp <;>
    omega

/-- Two odd integers whose product is a square cannot sum to zero modulo 8.
This avoids extracting their common squarefree part. -/
theorem odd_square_product_pair_not_zero_mod_eight
    (a b : ℕ) (ha : a % 2 = 1) (hb : b % 2 = 1)
    (hsq : IsSquare (a * b)) : (a + b) % 8 ≠ 0 := by
  obtain ⟨u, hu⟩ := hsq
  have huodd : u % 2 = 1 := by
    have habodd : (a * b) % 2 = 1 := Nat.odd_mul_odd ha hb
    have hu2odd : (u ^ 2) % 2 = 1 := by simpa [pow_two, ← hu] using habodd
    by_contra h
    have hue : u % 2 = 0 := by omega
    have h2 : 2 ∣ u := Nat.dvd_of_mod_eq_zero hue
    have hu2even : 2 ∣ u ^ 2 := by
      simpa [pow_two] using (dvd_mul_of_dvd_left h2 u)
    omega
  have hab8 : (a * b) % 8 = 1 := by
    simpa [pow_two, ← hu] using oddSquare_mod_eight u huodd
  have hprodmod : ((a % 8) * (b % 8)) % 8 = (a * b) % 8 :=
    (Nat.mod_modEq a 8).mul (Nat.mod_modEq b 8)
  intro hsum
  have halt : a % 8 < 8 := Nat.mod_lt a (by omega)
  have hblt : b % 8 < 8 := Nat.mod_lt b (by omega)
  interval_cases hresA : a % 8 <;> interval_cases hresB : b % 8 <;>
    norm_num [hresA, hresB] at hprodmod <;>
    omega

/-- If the odd paired coefficients have square product, their two quartic
terms cannot alone produce the target residue 8 modulo 16. -/
theorem odd_square_product_pairQuartic_ne_eight_mod_sixteen
    (a b x y : ℕ) (ha : a % 2 = 1) (hb : b % 2 = 1)
    (hsq : IsSquare (a * b)) :
    (a * x ^ 4 + b * y ^ 4) % 16 ≠ 8 := by
  have hx4 : x ^ 4 ≡ x % 2 [MOD 16] := by
    change x ^ 4 % 16 = (x % 2) % 16
    rw [Nat.mod_eq_of_lt (by omega : x % 2 < 16)]
    exact fourthPower_mod_sixteen x
  have hy4 : y ^ 4 ≡ y % 2 [MOD 16] := by
    change y ^ 4 % 16 = (y % 2) % 16
    rw [Nat.mod_eq_of_lt (by omega : y % 2 < 16)]
    exact fourthPower_mod_sixteen y
  have hred := ((Nat.ModEq.refl a).mul hx4).add ((Nat.ModEq.refl b).mul hy4)
  intro h8
  have hred8 : (a * (x % 2) + b * (y % 2)) % 16 = 8 := by
    have hred' : (a * x ^ 4 + b * y ^ 4) % 16 =
        (a * (x % 2) + b * (y % 2)) % 16 := hred
    exact hred'.symm.trans h8
  have hxlt : x % 2 < 2 := Nat.mod_lt x (by omega)
  have hylt : y % 2 < 2 := Nat.mod_lt y (by omega)
  interval_cases hx : x % 2 <;> interval_cases hy : y % 2
  · simp at hred8
  · simp only [mul_zero, mul_one, zero_add] at hred8
    omega
  · simp only [mul_zero, mul_one, add_zero] at hred8
    omega
  · simp only [mul_one] at hred8
    have hpair := odd_square_product_pair_not_zero_mod_eight a b ha hb hsq
    omega

/-- Two coefficients with the same odd squarefree part cannot add to zero
modulo 8 when their remaining factors are odd squares. -/
theorem oddPairedCoefficients_mod_eight
    (A s t : ℕ) (hA : A % 2 = 1) (hs : s % 2 = 1) (ht : t % 2 = 1) :
    (A * s ^ 2 + A * t ^ 2) % 8 ≠ 0 := by
  have hs2 := oddSquare_mod_eight s hs
  have ht2 := oddSquare_mod_eight t ht
  have hpair : (A * s ^ 2 + A * t ^ 2) % 8 = (2 * A) % 8 := by
    have hsm : s ^ 2 ≡ 1 [MOD 8] := hs2
    have htm : t ^ 2 ≡ 1 [MOD 8] := ht2
    have hm := ((Nat.ModEq.refl A).mul hsm).add ((Nat.ModEq.refl A).mul htm)
    simpa [Nat.ModEq, two_mul] using hm
  rw [hpair]
  omega

/-- The paired terms alone cannot attain the 2-adic target residue 8. -/
theorem oddPairedQuartic_ne_eight_mod_sixteen
    (A s t x y : ℕ) (hA : A % 2 = 1)
    (hs : s % 2 = 1) (ht : t % 2 = 1) :
    (A * s ^ 2 * x ^ 4 + A * t ^ 2 * y ^ 4) % 16 ≠ 8 := by
  have hx4 : x ^ 4 ≡ x % 2 [MOD 16] := by
    change x ^ 4 % 16 = (x % 2) % 16
    rw [Nat.mod_eq_of_lt (by omega : x % 2 < 16)]
    exact fourthPower_mod_sixteen x
  have hy4 : y ^ 4 ≡ y % 2 [MOD 16] := by
    change y ^ 4 % 16 = (y % 2) % 16
    rw [Nat.mod_eq_of_lt (by omega : y % 2 < 16)]
    exact fourthPower_mod_sixteen y
  have hred := ((Nat.ModEq.refl (A * s ^ 2)).mul hx4).add
    ((Nat.ModEq.refl (A * t ^ 2)).mul hy4)
  intro h8
  have hred8 : (A * s ^ 2 * (x % 2) + A * t ^ 2 * (y % 2)) % 16 = 8 := by
    have hred' : (A * s ^ 2 * x ^ 4 + A * t ^ 2 * y ^ 4) % 16 =
        (A * s ^ 2 * (x % 2) + A * t ^ 2 * (y % 2)) % 16 := hred
    rw [← hred']
    exact h8
  have hxlt : x % 2 < 2 := Nat.mod_lt x (by omega)
  have hylt : y % 2 < 2 := Nat.mod_lt y (by omega)
  interval_cases hx : x % 2 <;> interval_cases hy : y % 2
  · simp at hred8
  · simp only [mul_zero, mul_one, zero_add] at hred8
    have hodd : (A * t ^ 2) % 2 = 1 := by
      have htm : t ≡ 1 [MOD 2] := ht
      have hAm : A ≡ 1 [MOD 2] := hA
      simpa [Nat.ModEq] using hAm.mul (htm.pow 2)
    omega
  · simp only [mul_zero, mul_one, add_zero] at hred8
    have hodd : (A * s ^ 2) % 2 = 1 := by
      have hsm : s ≡ 1 [MOD 2] := hs
      have hAm : A ≡ 1 [MOD 2] := hA
      simpa [Nat.ModEq] using hAm.mul (hsm.pow 2)
    omega
  · simp only [mul_one] at hred8
    have hpair := oddPairedCoefficients_mod_eight A s t hA hs ht
    omega

/-- At the 2-adic target, at least one of the two unpaired terms survives
modulo 16.  This is the exact parity step used before quadratic Hensel
lifting. -/
theorem mixedQuartic_unpaired_term_nonzero_mod_sixteen
    (A s t c d x y z w : ℕ)
    (hA : A % 2 = 1) (hs : s % 2 = 1) (ht : t % 2 = 1)
    (hF : (A * s ^ 2 * x ^ 4 + A * t ^ 2 * y ^ 4 +
      c * z ^ 4 + d * w ^ 4) % 16 = 8) :
    (c * z ^ 4) % 16 ≠ 0 ∨ (d * w ^ 4) % 16 ≠ 0 := by
  by_contra h
  simp only [not_or, not_not] at h
  have hcz : c * z ^ 4 ≡ 0 [MOD 16] := h.1
  have hdw : d * w ^ 4 ≡ 0 [MOD 16] := h.2
  have hp := (((Nat.ModEq.refl
    (A * s ^ 2 * x ^ 4 + A * t ^ 2 * y ^ 4)).add hcz).add hdw)
  have hp' : (A * s ^ 2 * x ^ 4 + A * t ^ 2 * y ^ 4 +
      c * z ^ 4 + d * w ^ 4) % 16 =
      (A * s ^ 2 * x ^ 4 + A * t ^ 2 * y ^ 4) % 16 := by
    simpa [Nat.ModEq] using hp
  exact oddPairedQuartic_ne_eight_mod_sixteen A s t x y hA hs ht
    (hp'.symm.trans hF)

/-- A nonzero canonical quartic term modulo 16 must have an odd coefficient
and an odd variable. -/
theorem canonicalPart_term_nonzero_mod_sixteen_odd
    (a : CanonicalParts) (x : ℕ)
    (h : (a.val * x ^ 4) % 16 ≠ 0) :
    a.val % 2 = 1 ∧ x % 2 = 1 := by
  constructor
  · by_contra haodd
    have hae : a.val % 2 = 0 := by omega
    have h2 : 2 ∣ a.val := Nat.dvd_of_mod_eq_zero hae
    have h16 : 16 ∣ a.val := by
      simpa using canonicalPart_prime_fourth_dvd a 2 (by norm_num) h2
    exact h (Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_left h16 _))
  · by_contra hxodd
    have hxe : x % 2 = 0 := by omega
    have hx16 : 16 ∣ x ^ 4 := Nat.dvd_of_mod_eq_zero
      ((fourthPower_mod_sixteen x).trans hxe)
    exact h (Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_right hx16 _))

/-- A single canonical quartic term can never have residue 8 modulo 16. -/
theorem canonicalPart_term_ne_eight_mod_sixteen
    (a : CanonicalParts) (x : ℕ) : (a.val * x ^ 4) % 16 ≠ 8 := by
  intro h8
  have hnonzero : (a.val * x ^ 4) % 16 ≠ 0 := by omega
  obtain ⟨haodd, hxodd⟩ := canonicalPart_term_nonzero_mod_sixteen_odd a x hnonzero
  have hx4 : x ^ 4 ≡ 1 [MOD 16] := by
    change x ^ 4 % 16 = 1 % 16
    simp [fourthPower_mod_sixteen x, hxodd]
  have hmod : (a.val * x ^ 4) % 16 = a.val % 16 := by
    simpa [Nat.ModEq] using (Nat.ModEq.refl a.val).mul hx4
  have ha8 : a.val % 16 = 8 := hmod.symm.trans h8
  omega

/-- With canonical unpaired coefficients, the parity step identifies an odd
quadratic coordinate for the mixed form at the prime two. -/
theorem mixedQuartic_unpaired_odd_term
    (c d : CanonicalParts) (A s t x y z w : ℕ)
    (hA : A % 2 = 1) (hs : s % 2 = 1) (ht : t % 2 = 1)
    (hF : (A * s ^ 2 * x ^ 4 + A * t ^ 2 * y ^ 4 +
      c.val * z ^ 4 + d.val * w ^ 4) % 16 = 8) :
    (c.val % 2 = 1 ∧ z % 2 = 1) ∨
      (d.val % 2 = 1 ∧ w % 2 = 1) := by
  rcases mixedQuartic_unpaired_term_nonzero_mod_sixteen
      A s t c.val d.val x y z w hA hs ht hF with hc | hd
  · exact Or.inl (canonicalPart_term_nonzero_mod_sixteen_odd c z hc)
  · exact Or.inr (canonicalPart_term_nonzero_mod_sixteen_odd d w hd)

/-- If a product of an integer and a square is odd, each factor is odd. -/
theorem odd_factors_of_odd_square_product (A s : ℕ)
    (h : (A * s ^ 2) % 2 = 1) : A % 2 = 1 ∧ s % 2 = 1 := by
  constructor
  · by_contra hA
    have hAe : A % 2 = 0 := by omega
    have h2 : 2 ∣ A := Nat.dvd_of_mod_eq_zero hAe
    have hprod : 2 ∣ A * s ^ 2 := dvd_mul_of_dvd_left h2 _
    exact (by omega : False)
  · by_contra hs
    have hse : s % 2 = 0 := by omega
    have h2 : 2 ∣ s := Nat.dvd_of_mod_eq_zero hse
    have hs2 : 2 ∣ s ^ 2 := by
      simpa only [pow_two] using (dvd_mul_of_dvd_left h2 s)
    have hprod : 2 ∣ A * s ^ 2 := dvd_mul_of_dvd_right hs2 _
    exact (by omega : False)

/-- The dyadic parity conclusion requires only that the two paired odd
coefficients have square product; no squarefree-part extraction is needed. -/
theorem squareProduct_unpaired_odd_at_dyadic_target
    (a b c d : CanonicalParts) (x y z w : ℕ)
    (hsq : IsSquare (a.val * b.val))
    (hF : (a.val * x ^ 4 + b.val * y ^ 4 +
      c.val * z ^ 4 + d.val * w ^ 4) % 16 = 8) :
    (c.val % 2 = 1 ∧ z % 2 = 1) ∨
      (d.val % 2 = 1 ∧ w % 2 = 1) := by
  by_cases hcz : (c.val * z ^ 4) % 16 ≠ 0
  · exact Or.inl (canonicalPart_term_nonzero_mod_sixteen_odd c z hcz)
  by_cases hdw : (d.val * w ^ 4) % 16 ≠ 0
  · exact Or.inr (canonicalPart_term_nonzero_mod_sixteen_odd d w hdw)
  have hcz0 : c.val * z ^ 4 ≡ 0 [MOD 16] := not_not.mp hcz
  have hdw0 : d.val * w ^ 4 ≡ 0 [MOD 16] := not_not.mp hdw
  have hpairmod :=
    (((Nat.ModEq.refl (a.val * x ^ 4 + b.val * y ^ 4)).add hcz0).add hdw0)
  have hpair8 : (a.val * x ^ 4 + b.val * y ^ 4) % 16 = 8 := by
    have hp : (a.val * x ^ 4 + b.val * y ^ 4 +
        c.val * z ^ 4 + d.val * w ^ 4) % 16 =
        (a.val * x ^ 4 + b.val * y ^ 4) % 16 := by
      simpa [Nat.ModEq] using hpairmod
    exact hp.symm.trans hF
  have hax : (a.val * x ^ 4) % 16 ≠ 0 := by
    intro hax0
    have hby8 : (b.val * y ^ 4) % 16 = 8 := by omega
    exact canonicalPart_term_ne_eight_mod_sixteen b y hby8
  have hby : (b.val * y ^ 4) % 16 ≠ 0 := by
    intro hby0
    have hax8 : (a.val * x ^ 4) % 16 = 8 := by omega
    exact canonicalPart_term_ne_eight_mod_sixteen a x hax8
  have haodd : a.val % 2 = 1 :=
    (canonicalPart_term_nonzero_mod_sixteen_odd a x hax).1
  have hbodd : b.val % 2 = 1 :=
    (canonicalPart_term_nonzero_mod_sixteen_odd b y hby).1
  exact False.elim (odd_square_product_pairQuartic_ne_eight_mod_sixteen
    a.val b.val x y haodd hbodd hsq hpair8)

/-- The dyadic parity statement in the explicit common-squarefree-part
presentation sometimes used for the mixed exceptional condition. -/
theorem mixedExceptional_unpaired_odd_of_factorization
    (a b c d : CanonicalParts) (A s t x y z w : ℕ)
    (ha : a.val = A * s ^ 2) (hb : b.val = A * t ^ 2)
    (hF : (a.val * x ^ 4 + b.val * y ^ 4 +
      c.val * z ^ 4 + d.val * w ^ 4) % 16 = 8) :
    (c.val % 2 = 1 ∧ z % 2 = 1) ∨
      (d.val % 2 = 1 ∧ w % 2 = 1) := by
  have hsq : IsSquare (a.val * b.val) := by
    refine ⟨A * s * t, ?_⟩
    rw [ha, hb]
    ring
  exact squareProduct_unpaired_odd_at_dyadic_target a b c d x y z w hsq hF

/-- The mixed exceptional rational fourth-power condition itself implies
the dyadic parity conclusion, with no extra factorization hypothesis. -/
theorem mixedExceptional_unpaired_odd_at_dyadic_target
    (a b c d : CanonicalParts) (x y z w : ℕ)
    (hm : MixedExceptional (a.val : ℚ) (b.val : ℚ)
      (c.val : ℚ) (d.val : ℚ))
    (hF : (a.val * x ^ 4 + b.val * y ^ 4 +
      c.val * z ^ 4 + d.val * w ^ 4) % 16 = 8) :
    (c.val % 2 = 1 ∧ z % 2 = 1) ∨
      (d.val % 2 = 1 ∧ w % 2 = 1) := by
  have hsq : IsSquare (a.val * b.val) :=
    mixedExceptional_nat_paired_product_square
      a.val b.val c.val d.val a.property.pos b.property.pos
      c.property.pos d.property.pos hm
  exact squareProduct_unpaired_odd_at_dyadic_target a b c d x y z w hsq hF

/-- A canonical quartic value congruent to eight modulo sixteen has a
coefficient-variable pair that is odd. -/
theorem canonicalTuple_dyadic_unit_coordinate
    (d : Fin 4 → CanonicalParts) (x : Fin 4 → ℕ)
    (hF : (∑ i : Fin 4, (d i).val * x i ^ 4) % 16 = 8) :
    ∃ i : Fin 4, (d i).val % 2 = 1 ∧ x i % 2 = 1 := by
  have hnonzero : ∃ i : Fin 4, ((d i).val * x i ^ 4) % 16 ≠ 0 := by
    by_contra h
    push Not at h
    have hsum : (∑ i : Fin 4, (d i).val * x i ^ 4) % 16 = 0 := by
      simp only [Fin.sum_univ_four]
      have h0 := h 0
      have h1 := h 1
      have h2 := h 2
      have h3 := h 3
      omega
    omega
  obtain ⟨i, hi⟩ := hnonzero
  exact ⟨i, canonicalPart_term_nonzero_mod_sixteen_odd (d i) (x i) hi⟩

/-- At the dyadic place, a represented exceptional square-determinant
quartic target makes the associated diagonal quadratic form isotropic. -/
theorem canonicalTuple_dyadic_square_quadratic_zero
    (place : HeightOneSpectrum (𝓞 ℚ)) (d : Fin 4 → CanonicalParts)
    (x : Fin 4 → ℕ)
    (hdyadic : (finitePlacePadicPrime place : ℕ) = 2)
    (hF : (∑ i : Fin 4, (d i).val * x i ^ 4) % 16 = 8) :
    ∃ y : Fin 4 → place.adicCompletion ℚ,
      (∃ i : Fin 4, y i ≠ 0) ∧
        (∑ i : Fin 4,
          ((d i).val : place.adicCompletion ℚ) * y i ^ 2) = 0 := by
  obtain ⟨i, hdi, hxi⟩ := canonicalTuple_dyadic_unit_coordinate d x hF
  let N := ∑ j : Fin 4, (d j).val * x j ^ 4
  have hvalue : (∑ j : Fin 4, (d j).val * (x j ^ 2) ^ 2) = N := by
    unfold N
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hunit : ¬(finitePlacePadicPrime place : ℕ) ∣
      (d i).val * (x i ^ 2) ^ 2 := by
    rw [hdyadic]
    intro h
    have hmod : ((d i).val * (x i ^ 2) ^ 2) % 2 = 1 := by
      simp [Nat.mul_mod, Nat.pow_mod, hdi, hxi]
    exact (by omega : False)
  have hdiv : ((finitePlacePadicPrime place : ℕ) ≠ 2 ∧
      (finitePlacePadicPrime place : ℕ) ∣ N) ∨
      ((finitePlacePadicPrime place : ℕ) = 2 ∧ 8 ∣ N) := by
    right
    refine ⟨hdyadic, ?_⟩
    unfold N
    omega
  obtain ⟨y, hy, hzero⟩ :=
    finiteCompletion_integer_diagonal_zero_of_unit place
      (fun j => (d j).val) (fun j => x j ^ 2) i N hvalue hunit hdiv
  exact ⟨y, ⟨i, hy⟩, hzero⟩

/-- A mixed exceptional quartic value eight modulo sixteen produces a
nonzero zero of the *same* quadratic form used in its reciprocity argument. -/
theorem mixedExceptional_dyadic_quadratic_zero
    (place : HeightOneSpectrum (𝓞 ℚ))
    (a b c d : CanonicalParts) (t : ℚ) (x y z w : ℕ)
    (hdyadic : (finitePlacePadicPrime place : ℕ) = 2)
    (hm : MixedExceptional (a.val : ℚ) (b.val : ℚ)
      (c.val : ℚ) (d.val : ℚ))
    (hb : (b.val : ℚ) = (a.val : ℚ) * t ^ 2)
    (hF : (a.val * x ^ 4 + b.val * y ^ 4 +
      c.val * z ^ 4 + d.val * w ^ 4) % 16 = 8) :
    ∃ q : Fin 4 → place.adicCompletion ℚ,
      (∃ i : Fin 4, q i ≠ 0) ∧
        (a.val : place.adicCompletion ℚ) * q 0 ^ 2 +
        (c.val : place.adicCompletion ℚ) * q 1 ^ 2 +
        (d.val : place.adicCompletion ℚ) * q 2 ^ 2 +
        ((2 * (a.val : ℚ) * t : ℚ) : place.adicCompletion ℚ) * q 3 ^ 2 = 0 := by
  let N := a.val * x ^ 4 + b.val * y ^ 4 + c.val * z ^ 4 + d.val * w ^ 4
  let cf : Fin 4 → place.adicCompletion ℚ :=
    ![(a.val : place.adicCompletion ℚ),
      (c.val : place.adicCompletion ℚ),
      (d.val : place.adicCompletion ℚ),
      ((2 * (a.val : ℚ) * t : ℚ) : place.adicCompletion ℚ)]
  let zv : Fin 4 → place.adicCompletion ℚ :=
    ![(x : place.adicCompletion ℚ) ^ 2 -
        (t : place.adicCompletion ℚ) * (y : place.adicCompletion ℚ) ^ 2,
      (z : place.adicCompletion ℚ) ^ 2,
      (w : place.adicCompletion ℚ) ^ 2,
      (x : place.adicCompletion ℚ) * (y : place.adicCompletion ℚ)]
  have hbK : (b.val : place.adicCompletion ℚ) =
      (a.val : place.adicCompletion ℚ) *
        (t : place.adicCompletion ℚ) ^ 2 := by
    exact_mod_cast hb
  have hcoef :
      ((2 * (a.val : ℚ) * t : ℚ) : place.adicCompletion ℚ) =
        2 * (a.val : place.adicCompletion ℚ) *
          (t : place.adicCompletion ℚ) := by
    norm_cast
  have hvalue : (∑ j : Fin 4, cf j * zv j ^ 2) =
      (N : place.adicCompletion ℚ) := by
    simp only [Fin.sum_univ_four]
    dsimp [cf, zv]
    rw [hcoef]
    rw [← mixedQuartic_quadratic_identity
      (a.val : place.adicCompletion ℚ)
      (b.val : place.adicCompletion ℚ)
      (c.val : place.adicCompletion ℚ)
      (d.val : place.adicCompletion ℚ)
      (t : place.adicCompletion ℚ)
      (x : place.adicCompletion ℚ) (y : place.adicCompletion ℚ)
      (z : place.adicCompletion ℚ) (w : place.adicCompletion ℚ) hbK]
    unfold N
    norm_cast
  have hN : 8 ∣ N := by
    unfold N
    omega
  rcases mixedExceptional_unpaired_odd_at_dyadic_target
      a b c d x y z w hm hF with ⟨hcodd, hzodd⟩ | ⟨hdodd, hwodd⟩
  · have hunit : ¬(finitePlacePadicPrime place : ℕ) ∣ c.val * z ^ 4 := by
      rw [hdyadic]
      intro h
      have hmod : (c.val * z ^ 4) % 2 = 1 := by
        simp [Nat.mul_mod, Nat.pow_mod, hcodd, hzodd]
      omega
    have hterm : cf 1 * zv 1 ^ 2 ≠ 0 := by
      have hcast : ((c.val * z ^ 4 : ℕ) : place.adicCompletion ℚ) ≠ 0 := by
        exact_mod_cast (show c.val * z ^ 4 ≠ 0 by
          intro h0
          have hmod : (c.val * z ^ 4) % 2 = 1 := by
            simp [Nat.mul_mod, Nat.pow_mod, hcodd, hzodd]
          omega)
      have heq : cf 1 * zv 1 ^ 2 =
          ((c.val * z ^ 4 : ℕ) : place.adicCompletion ℚ) := by
        dsimp [cf, zv]
        norm_cast
        ring
      rw [heq]
      exact hcast
    have hsmall : finiteCompletionPerturbationSmall place
        ((N : place.adicCompletion ℚ) / (cf 1 * zv 1 ^ 2)) := by
      convert finiteCompletion_small_of_dyadic_nat_dvd_unit
        place N (c.val * z ^ 4) hdyadic hN hunit using 1
      dsimp [cf, zv]
      congr 1
      norm_cast
      ring
    obtain ⟨q, hq, hzero⟩ :=
      finiteCompletion_diagonal_quadratic_perturb_fin4
        place cf zv 1 (N : place.adicCompletion ℚ) hvalue hterm hsmall
    refine ⟨q, ⟨1, hq⟩, ?_⟩
    simpa [Fin.sum_univ_four, cf] using hzero

  · have hunit : ¬(finitePlacePadicPrime place : ℕ) ∣ d.val * w ^ 4 := by
      rw [hdyadic]
      intro h
      have hmod : (d.val * w ^ 4) % 2 = 1 := by
        simp [Nat.mul_mod, Nat.pow_mod, hdodd, hwodd]
      omega
    have hterm : cf 2 * zv 2 ^ 2 ≠ 0 := by
      have hcast : ((d.val * w ^ 4 : ℕ) : place.adicCompletion ℚ) ≠ 0 := by
        exact_mod_cast (show d.val * w ^ 4 ≠ 0 by
          intro h0
          have hmod : (d.val * w ^ 4) % 2 = 1 := by
            simp [Nat.mul_mod, Nat.pow_mod, hdodd, hwodd]
          omega)
      have heq : cf 2 * zv 2 ^ 2 =
          ((d.val * w ^ 4 : ℕ) : place.adicCompletion ℚ) := by
        dsimp [cf, zv]
        norm_cast
        ring
      rw [heq]
      exact hcast
    have hsmall : finiteCompletionPerturbationSmall place
        ((N : place.adicCompletion ℚ) / (cf 2 * zv 2 ^ 2)) := by
      convert finiteCompletion_small_of_dyadic_nat_dvd_unit
        place N (d.val * w ^ 4) hdyadic hN hunit using 1
      dsimp [cf, zv]
      congr 1
      norm_cast
      ring
    obtain ⟨q, hq, hzero⟩ :=
      finiteCompletion_diagonal_quadratic_perturb_fin4
        place cf zv 2 (N : place.adicCompletion ℚ) hvalue hterm hsmall
    refine ⟨q, ⟨2, hq⟩, ?_⟩
    simpa [Fin.sum_univ_four, cf] using hzero

/-- A missing residue class at any divisor of the modulus makes the full
quartic local count zero. This is the step from one local obstruction to the
zero-density assertion in the sieve. -/
theorem localCount_zero_of_no_solution_mod_divisor
    (d : Fin 4 → ℕ) (M m a : ℕ) (hM : M ≠ 0) (hm : m ∣ M)
    (hno : ∀ y : Fin 4 → ZMod m,
      quarticFormMod m d y ≠ (a : ZMod m)) :
    @localCount d M a ⟨hM⟩ = 0 := by
  classical
  letI : NeZero M := ⟨hM⟩
  change Fintype.card
    {x : Fin 4 → ZMod M // quarticFormMod M d x = (a : ZMod M)} = 0
  apply Fintype.card_eq_zero_iff.mpr
  refine ⟨fun ⟨x, hx⟩ => ?_⟩
  let y : Fin 4 → ZMod m := fun i => ZMod.castHom hm (ZMod m) (x i)
  have hy : quarticFormMod m d y = (a : ZMod m) := by
    have h := congrArg (ZMod.castHom hm (ZMod m)) hx
    simpa [quarticFormMod, y, map_sum, map_mul, map_pow] using h
  exact hno y hy

/-- Reordering the four variables and their coefficients preserves the
quartic local count. -/
theorem localCount_perm
    (d : Fin 4 → ℕ) (M A : ℕ) [NeZero M]
    (σ : Equiv.Perm (Fin 4)) :
    localCount (fun j => d (σ j)) M A = localCount d M A := by
  classical
  let e : (Fin 4 → ZMod M) ≃ (Fin 4 → ZMod M) :=
    { toFun := fun x j => x (σ j)
      invFun := fun y j => y (σ.symm j)
      left_inv := by intro x; funext j; simp
      right_inv := by intro y; funext j; simp }
  have hform (x : Fin 4 → ZMod M) :
      quarticFormMod M (fun j => d (σ j)) (e x) =
        quarticFormMod M d x := by
    unfold quarticFormMod
    exact Fintype.sum_equiv σ
      (fun j : Fin 4 => (d (σ j) : ZMod M) * x (σ j) ^ 4)
      (fun j : Fin 4 => (d j : ZMod M) * x j ^ 4)
      (by intro j; rfl)
  let eSub :
      {x : Fin 4 → ZMod M // quarticFormMod M d x = (A : ZMod M)} ≃
      {x : Fin 4 → ZMod M //
        quarticFormMod M (fun j => d (σ j)) x = (A : ZMod M)} :=
    e.subtypeEquiv (fun x => by simp only [hform])
  exact (Fintype.card_congr eSub).symm

/-- Read a quartic solution in `ZMod m` as a congruence for the canonical
natural representatives of its coordinates. -/
theorem quartic_solution_nat_val
    (d : Fin 4 → ℕ) (m a : ℕ) [NeZero m] (ha : a < m)
    (x : Fin 4 → ZMod m)
    (hsol : (∑ j : Fin 4, (d j : ZMod m) * x j ^ 4) = (a : ZMod m)) :
    (∑ j : Fin 4, d j * (x j).val ^ 4) % m = a := by
  have hcast (j : Fin 4) : (((x j).val : ℕ) : ZMod m) = x j := by
    exact ZMod.natCast_zmod_val (x j)
  have hcastsol :
      ((∑ j : Fin 4, d j * (x j).val ^ 4 : ℕ) : ZMod m) = (a : ZMod m) := by
    simpa only [Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, hcast] using hsol
  have hmod := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hcastsol
  simpa [Nat.mod_eq_of_lt ha] using hmod

/-- At an odd anisotropic finite place, the valuation-one residue class is
impossible modulo the square of the local prime. -/
theorem anisotropic_odd_prime_excludes_prime_square
    (place : HeightOneSpectrum (𝓞 ℚ))
    (d : Fin 4 → CanonicalParts)
    (hodd : (finitePlacePadicPrime place : ℕ) ≠ 2)
    (haniso : ∀ y : Fin 4 → place.adicCompletion ℚ,
      (∑ j : Fin 4, ((d j).val : place.adicCompletion ℚ) * y j ^ 4) = 0 →
      ∀ j : Fin 4, y j = 0) :
    ∀ x : Fin 4 → ZMod ((finitePlacePadicPrime place : ℕ) ^ 2),
      (∑ j : Fin 4, ((d j).val :
          ZMod ((finitePlacePadicPrime place : ℕ) ^ 2)) * x j ^ 4) ≠
        ((finitePlacePadicPrime place : ℕ) :
          ZMod ((finitePlacePadicPrime place : ℕ) ^ 2)) := by
  intro x hsol
  let p : ℕ := finitePlacePadicPrime place
  have hp : p.Prime := (finitePlacePadicPrime place).2
  have hp2 : p ^ 2 ≠ 0 := by exact pow_ne_zero 2 hp.ne_zero
  letI : NeZero (p ^ 2) := ⟨hp2⟩
  let xn : Fin 4 → ℕ := fun j => (x j).val
  have hsolNat : (∑ j : Fin 4, (d j).val * xn j ^ 4) % (p ^ 2) = p := by
    have hlt : p < p ^ 2 := by
      have hp2' := hp.two_le
      nlinarith
    exact quartic_solution_nat_val (fun j => (d j).val)
      (p ^ 2) p hlt x hsol
  obtain ⟨i, hdi, hxi⟩ :=
    canonicalTuple_nat_unit_coordinate_of_target d p hp xn hsolNat
  obtain ⟨y, hy, hzero⟩ :=
    finiteCompletion_quartic_hensel_of_prime_square_target
      place d xn i hodd hsolNat hdi hxi
  exact hy (haniso y hzero i)

/-- Dyadic valuation-three targets are impossible when the associated
diagonal quadratic form is anisotropic at the dyadic place. -/
theorem anisotropic_square_dyadic_excludes_sixteen
    (place : HeightOneSpectrum (𝓞 ℚ))
    (d : Fin 4 → CanonicalParts)
    (hdyadic : (finitePlacePadicPrime place : ℕ) = 2)
    (haniso : ∀ y : Fin 4 → place.adicCompletion ℚ,
      (∑ j : Fin 4, ((d j).val : place.adicCompletion ℚ) * y j ^ 2) = 0 →
      ∀ j : Fin 4, y j = 0) :
    ∀ x : Fin 4 → ZMod 16,
      (∑ j : Fin 4, ((d j).val : ZMod 16) * x j ^ 4) ≠ (8 : ZMod 16) := by
  intro x hsol
  have hF : (∑ j : Fin 4, (d j).val * (x j).val ^ 4) % 16 = 8 :=
    quartic_solution_nat_val (fun j => (d j).val) 16 8 (by decide) x hsol
  obtain ⟨y, ⟨i, hy⟩, hzero⟩ :=
    canonicalTuple_dyadic_square_quadratic_zero place d
      (fun j => (x j).val) hdyadic hF
  exact hy (haniso y hzero i)

/-- The same dyadic exclusion for the mixed exceptional form, in its
specified coefficient order and with the rational quadratic parameter. -/
theorem anisotropic_mixed_dyadic_excludes_sixteen
    (place : HeightOneSpectrum (𝓞 ℚ))
    (a b c d : CanonicalParts) (t : ℚ)
    (hdyadic : (finitePlacePadicPrime place : ℕ) = 2)
    (hm : MixedExceptional (a.val : ℚ) (b.val : ℚ)
      (c.val : ℚ) (d.val : ℚ))
    (hb : (b.val : ℚ) = (a.val : ℚ) * t ^ 2)
    (haniso : ∀ q : Fin 4 → place.adicCompletion ℚ,
      (a.val : place.adicCompletion ℚ) * q 0 ^ 2 +
        (c.val : place.adicCompletion ℚ) * q 1 ^ 2 +
        (d.val : place.adicCompletion ℚ) * q 2 ^ 2 +
        ((2 * (a.val : ℚ) * t : ℚ) : place.adicCompletion ℚ) * q 3 ^ 2 = 0 →
      ∀ j : Fin 4, q j = 0) :
    ∀ x : Fin 4 → ZMod 16,
      (∑ j : Fin 4, ((![a, b, c, d] j).val : ZMod 16) * x j ^ 4) ≠
        (8 : ZMod 16) := by
  intro x hsol
  have hF : (a.val * (x 0).val ^ 4 + b.val * (x 1).val ^ 4 +
      c.val * (x 2).val ^ 4 + d.val * (x 3).val ^ 4) % 16 = 8 := by
    have h := quartic_solution_nat_val
      (fun j => (![a, b, c, d] j).val) 16 8 (by decide) x hsol
    simpa [Fin.sum_univ_four] using h
  obtain ⟨q, ⟨i, hi⟩, hzero⟩ :=
    mixedExceptional_dyadic_quadratic_zero place a b c d t
      (x 0).val (x 1).val (x 2).val (x 3).val hdyadic hm hb hF
  exact hi (haniso q hzero i)

/-- A diagonal quadratic anisotropy witness rules out a nonzero zero of the
associated quartic at the same finite place. -/
theorem squareQuadratic_anisotropic_implies_quartic_anisotropic
    (place : HeightOneSpectrum (𝓞 ℚ)) (d : Fin 4 → CanonicalParts)
    (haniso : ∀ y : Fin 4 → place.adicCompletion ℚ,
      (∑ j : Fin 4, ((d j).val : place.adicCompletion ℚ) * y j ^ 2) = 0 →
      ∀ j : Fin 4, y j = 0) :
    ∀ x : Fin 4 → place.adicCompletion ℚ,
      (∑ j : Fin 4, ((d j).val : place.adicCompletion ℚ) * x j ^ 4) = 0 →
      ∀ j : Fin 4, x j = 0 := by
  intro x hzero i
  have hQ : (∑ j : Fin 4,
      ((d j).val : place.adicCompletion ℚ) * (x j ^ 2) ^ 2) = 0 := by
    simpa only [← pow_mul, show 2 * 2 = 4 by decide] using hzero
  have hi := haniso (fun j => x j ^ 2) hQ i
  exact mul_self_eq_zero.mp (by simpa [pow_two] using hi)

/-- If the diagonal quadratic form is anisotropic at one finite place, the
prescribed small-modulus progression has zero quartic local count. -/
theorem squareQuadratic_anisotropic_localCount_zero
    (place : HeightOneSpectrum (𝓞 ℚ)) (d : Fin 4 → CanonicalParts)
    (M a : ℕ) (hM : M ≠ 0)
    (hQ : ∀ y : Fin 4 → place.adicCompletion ℚ,
      (∑ j : Fin 4, ((d j).val : place.adicCompletion ℚ) * y j ^ 2) = 0 →
      ∀ j : Fin 4, y j = 0)
    (h16 : 16 ∣ M) (ha16 : a % 16 = 8)
    (hoddTargets : ∀ p : ℕ, p.Prime → p ≠ 2 →
      (∃ i : Fin 4, p ∣ (d i).val) →
      p ^ 2 ∣ M ∧ a % (p ^ 2) = p) :
    @localCount (fun i => (d i).val) M a ⟨hM⟩ = 0 := by
  let p : ℕ := finitePlacePadicPrime place
  have hp : p.Prime := (finitePlacePadicPrime place).2
  by_cases hdyadic : p = 2
  · have hno := anisotropic_square_dyadic_excludes_sixteen
      place d hdyadic hQ
    have htarget : (a : ZMod 16) = (8 : ZMod 16) := by
      apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
      simpa using ha16
    apply localCount_zero_of_no_solution_mod_divisor
      (fun i => (d i).val) M 16 a hM h16
    intro y hy
    exact hno y (hy.trans htarget)
  · by_cases hgood : ∀ i : Fin 4, ¬p ∣ (d i).val
    · obtain ⟨y, ⟨i, hi⟩, hzero⟩ :=
        finiteCompletion_quadratic_nontrivial_zero_of_odd_good_prime
          place hdyadic (fun i => (d i).val) hgood
      exact (hi (hQ y hzero i)).elim
    · push Not at hgood
      obtain ⟨i, hdi⟩ := hgood
      obtain ⟨hm, ha⟩ := hoddTargets p hp hdyadic ⟨i, hdi⟩
      have hquartic := squareQuadratic_anisotropic_implies_quartic_anisotropic
        place d hQ
      have hno := anisotropic_odd_prime_excludes_prime_square
        place d hdyadic hquartic
      have htarget : (a : ZMod (p ^ 2)) = (p : ZMod (p ^ 2)) := by
        apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
        have hlt : p < p ^ 2 := by
          have hp2 := hp.two_le
          nlinarith
        simpa [Nat.mod_eq_of_lt hlt] using ha
      apply localCount_zero_of_no_solution_mod_divisor
        (fun i => (d i).val) M (p ^ 2) a hM hm
      intro y hy
      exact hno y (hy.trans htarget)

/-- The square-determinant exceptional family is removed by the prescribed
dyadic and odd coefficient-prime congruences. -/
theorem squareExceptional_localCount_zero
    (d : Fin 4 → CanonicalParts)
    (k : ℚ) (hk : k ^ 2 = ∏ i : Fin 4, ((d i).val : ℚ))
    (M a : ℕ) (hM : M ≠ 0)
    (h16 : 16 ∣ M) (ha16 : a % 16 = 8)
    (hoddTargets : ∀ p : ℕ, p.Prime → p ≠ 2 →
      (∃ i : Fin 4, p ∣ (d i).val) →
      p ^ 2 ∣ M ∧ a % (p ^ 2) = p) :
    @localCount (fun i => (d i).val) M a ⟨hM⟩ = 0 := by
  have hk' : k ^ 2 = ((d 0).val : ℚ) * ((d 1).val : ℚ) *
      ((d 2).val : ℚ) * ((d 3).val : ℚ) := by
    simpa only [Fin.prod_univ_four] using hk
  obtain ⟨place, hQ4⟩ :=
    exists_finite_anisotropic_positive_square_det_diagonal
      ((d 0).val : ℚ) ((d 1).val : ℚ)
      ((d 2).val : ℚ) ((d 3).val : ℚ) k
      (canonical_coefficient_pos d 0) (canonical_coefficient_pos d 1)
      (canonical_coefficient_pos d 2) (canonical_coefficient_pos d 3)
      hk'
  have hQ : ∀ y : Fin 4 → place.adicCompletion ℚ,
      (∑ j : Fin 4, ((d j).val : place.adicCompletion ℚ) * y j ^ 2) = 0 →
      ∀ j : Fin 4, y j = 0 := by
    intro y hy j
    have hy4 : ((d 0).val : place.adicCompletion ℚ) * y 0 ^ 2 +
        ((d 1).val : place.adicCompletion ℚ) * y 1 ^ 2 +
        ((d 2).val : place.adicCompletion ℚ) * y 2 ^ 2 +
        ((d 3).val : place.adicCompletion ℚ) * y 3 ^ 2 = 0 := by
      simpa only [Fin.sum_univ_four] using hy
    obtain ⟨h0, h1, h2, h3⟩ := hQ4 (y 0) (y 1) (y 2) (y 3)
      (by exact_mod_cast hy4)
    fin_cases j <;> assumption
  exact squareQuadratic_anisotropic_localCount_zero
    place d M a hM hQ h16 ha16 hoddTargets

/-- Anisotropy of the mixed quadratic form excludes nonzero zeros of the
original quartic at that same finite place. -/
theorem mixedQuadratic_anisotropic_implies_quartic_anisotropic
    (place : HeightOneSpectrum (𝓞 ℚ))
    (a b c d : CanonicalParts) (t : ℚ)
    (hb : (b.val : ℚ) = (a.val : ℚ) * t ^ 2)
    (hQ : ∀ q : Fin 4 → place.adicCompletion ℚ,
      (a.val : place.adicCompletion ℚ) * q 0 ^ 2 +
        (c.val : place.adicCompletion ℚ) * q 1 ^ 2 +
        (d.val : place.adicCompletion ℚ) * q 2 ^ 2 +
        ((2 * (a.val : ℚ) * t : ℚ) : place.adicCompletion ℚ) * q 3 ^ 2 = 0 →
      ∀ j : Fin 4, q j = 0) :
    ∀ x : Fin 4 → place.adicCompletion ℚ,
      (∑ j : Fin 4,
        ((![a, b, c, d] j).val : place.adicCompletion ℚ) * x j ^ 4) = 0 →
      ∀ j : Fin 4, x j = 0 := by
  intro x hzero i
  by_contra hxi
  have hNZ : x 0 ≠ 0 ∨ x 1 ≠ 0 ∨ x 2 ≠ 0 ∨ x 3 ≠ 0 := by
    fin_cases i <;> simp_all
  have ht : (t : place.adicCompletion ℚ) ≠ 0 := by
    have htnat : t ≠ 0 := by
      intro ht0
      have hb0 : (b.val : ℚ) = 0 := by simpa [ht0] using hb
      exact (canonical_coefficient_pos (fun _ => b) 0).ne' hb0
    exact_mod_cast htnat
  have hbK : (b.val : place.adicCompletion ℚ) =
      (a.val : place.adicCompletion ℚ) *
        (t : place.adicCompletion ℚ) ^ 2 := by
    exact_mod_cast hb
  have hfour : (a.val : place.adicCompletion ℚ) * x 0 ^ 4 +
      (b.val : place.adicCompletion ℚ) * x 1 ^ 4 +
      (c.val : place.adicCompletion ℚ) * x 2 ^ 4 +
      (d.val : place.adicCompletion ℚ) * x 3 ^ 4 = 0 := by
    simpa [Fin.sum_univ_four] using hzero
  obtain ⟨U, V, W, Z, hNZQ, hQzero⟩ :=
    mixedQuartic_isotropic_forward
      (a.val : place.adicCompletion ℚ) (b.val : place.adicCompletion ℚ)
      (c.val : place.adicCompletion ℚ) (d.val : place.adicCompletion ℚ)
      (t : place.adicCompletion ℚ) (x 0) (x 1) (x 2) (x 3)
      ht hbK hNZ hfour
  let q : Fin 4 → place.adicCompletion ℚ := ![U, V, W, Z]
  have hQzero' : (a.val : place.adicCompletion ℚ) * q 0 ^ 2 +
      (c.val : place.adicCompletion ℚ) * q 1 ^ 2 +
      (d.val : place.adicCompletion ℚ) * q 2 ^ 2 +
      ((2 * (a.val : ℚ) * t : ℚ) : place.adicCompletion ℚ) * q 3 ^ 2 = 0 := by
    dsimp [q]
    convert hQzero using 1
    norm_cast
  have hzeroQ := hQ q hQzero'
  rcases hNZQ with hU | hV | hW | hZ
  · exact hU (hzeroQ 0)
  · exact hV (hzeroQ 1)
  · exact hW (hzeroQ 2)
  · exact hZ (hzeroQ 3)

/-- The mixed quadratic anisotropy witness rules out the sieve progression,
provided its good-prime local isotropy is available. -/
theorem mixedQuadratic_anisotropic_localCount_zero_ordered
    (place : HeightOneSpectrum (𝓞 ℚ))
    (a b c d : CanonicalParts) (t : ℚ)
    (M A : ℕ) (hM : M ≠ 0)
    (hmixed : MixedExceptional (a.val : ℚ) (b.val : ℚ)
      (c.val : ℚ) (d.val : ℚ))
    (hb : (b.val : ℚ) = (a.val : ℚ) * t ^ 2)
    (hQ : ∀ q : Fin 4 → place.adicCompletion ℚ,
      (a.val : place.adicCompletion ℚ) * q 0 ^ 2 +
        (c.val : place.adicCompletion ℚ) * q 1 ^ 2 +
        (d.val : place.adicCompletion ℚ) * q 2 ^ 2 +
        ((2 * (a.val : ℚ) * t : ℚ) : place.adicCompletion ℚ) * q 3 ^ 2 = 0 →
      ∀ j : Fin 4, q j = 0)
    (hgoodQ : (finitePlacePadicPrime place : ℕ) ≠ 2 →
      (∀ i : Fin 4,
        ¬(finitePlacePadicPrime place : ℕ) ∣ (![a, b, c, d] i).val) →
      ∃ q : Fin 4 → place.adicCompletion ℚ,
        (∃ i : Fin 4, q i ≠ 0) ∧
          (a.val : place.adicCompletion ℚ) * q 0 ^ 2 +
          (c.val : place.adicCompletion ℚ) * q 1 ^ 2 +
          (d.val : place.adicCompletion ℚ) * q 2 ^ 2 +
          ((2 * (a.val : ℚ) * t : ℚ) : place.adicCompletion ℚ) * q 3 ^ 2 = 0)
    (h16 : 16 ∣ M) (ha16 : A % 16 = 8)
    (hoddTargets : ∀ p : ℕ, p.Prime → p ≠ 2 →
      (∃ i : Fin 4, p ∣ (![a, b, c, d] i).val) →
      p ^ 2 ∣ M ∧ A % (p ^ 2) = p) :
    @localCount (fun i => (![a, b, c, d] i).val) M A ⟨hM⟩ = 0 := by
  let p : ℕ := finitePlacePadicPrime place
  have hp : p.Prime := (finitePlacePadicPrime place).2
  by_cases hdyadic : p = 2
  · have hno := anisotropic_mixed_dyadic_excludes_sixteen
      place a b c d t hdyadic hmixed hb hQ
    have htarget : (A : ZMod 16) = (8 : ZMod 16) := by
      apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
      simpa using ha16
    apply localCount_zero_of_no_solution_mod_divisor
      (fun i => (![a, b, c, d] i).val) M 16 A hM h16
    intro y hy
    exact hno y (hy.trans htarget)
  · by_cases hgood : ∀ i : Fin 4, ¬p ∣ (![a, b, c, d] i).val
    · obtain ⟨q, ⟨i, hi⟩, hzero⟩ := hgoodQ hdyadic hgood
      exact (hi (hQ q hzero i)).elim
    · push Not at hgood
      obtain ⟨i, hdi⟩ := hgood
      obtain ⟨hm, ha⟩ := hoddTargets p hp hdyadic ⟨i, hdi⟩
      have hquartic :=
        mixedQuadratic_anisotropic_implies_quartic_anisotropic
          place a b c d t hb hQ
      have hno := anisotropic_odd_prime_excludes_prime_square
        place (![a, b, c, d]) hdyadic hquartic
      have htarget : (A : ZMod (p ^ 2)) = (p : ZMod (p ^ 2)) := by
        apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
        have hlt : p < p ^ 2 := by
          have hp2 := hp.two_le
          nlinarith
        simpa [Nat.mod_eq_of_lt hlt] using ha
      apply localCount_zero_of_no_solution_mod_divisor
        (fun i => (![a, b, c, d] i).val) M (p ^ 2) A hM hm
      intro y hy
      exact hno y (hy.trans htarget)

/-- The mixed exceptional family, in its witnessing order, is removed by the
prescribed dyadic and odd coefficient-prime congruences. -/
theorem mixedExceptional_localCount_zero_ordered
    (a b c d : CanonicalParts)
    (hmixed : MixedExceptional (a.val : ℚ) (b.val : ℚ)
      (c.val : ℚ) (d.val : ℚ))
    (M A : ℕ) (hM : M ≠ 0)
    (h16 : 16 ∣ M) (ha16 : A % 16 = 8)
    (hoddTargets : ∀ p : ℕ, p.Prime → p ≠ 2 →
      (∃ i : Fin 4, p ∣ (![a, b, c, d] i).val) →
      p ^ 2 ∣ M ∧ A % (p ^ 2) = p) :
    @localCount (fun i => (![a, b, c, d] i).val) M A ⟨hM⟩ = 0 := by
  obtain ⟨t, k, ht, hcoef, hb, hdet⟩ :=
    mixedExceptional_positive_quadratic
      (a.val : ℚ) (b.val : ℚ) (c.val : ℚ) (d.val : ℚ)
      (by exact_mod_cast a.property.pos)
      (by exact_mod_cast b.property.pos)
      (by exact_mod_cast c.property.pos)
      (by exact_mod_cast d.property.pos) hmixed
  obtain ⟨place, hQ4⟩ :=
    exists_finite_anisotropic_positive_square_det_diagonal
      (a.val : ℚ) (c.val : ℚ) (d.val : ℚ)
      (2 * (a.val : ℚ) * t) k
      (by exact_mod_cast a.property.pos)
      (by exact_mod_cast c.property.pos)
      (by exact_mod_cast d.property.pos)
      hcoef hdet.symm
  have hQ : ∀ q : Fin 4 → place.adicCompletion ℚ,
      (a.val : place.adicCompletion ℚ) * q 0 ^ 2 +
        (c.val : place.adicCompletion ℚ) * q 1 ^ 2 +
        (d.val : place.adicCompletion ℚ) * q 2 ^ 2 +
        ((2 * (a.val : ℚ) * t : ℚ) : place.adicCompletion ℚ) * q 3 ^ 2 = 0 →
      ∀ j : Fin 4, q j = 0 := by
    intro q hzero j
    have hzero4 : ((a.val : ℚ) : place.adicCompletion ℚ) * q 0 ^ 2 +
        ((c.val : ℚ) : place.adicCompletion ℚ) * q 1 ^ 2 +
        ((d.val : ℚ) : place.adicCompletion ℚ) * q 2 ^ 2 +
        ((2 * (a.val : ℚ) * t : ℚ) : place.adicCompletion ℚ) * q 3 ^ 2 = 0 := by
      exact_mod_cast hzero
    obtain ⟨h0, h1, h2, h3⟩ := hQ4 (q 0) (q 1) (q 2) (q 3) hzero4
    fin_cases j <;> assumption
  have hgoodQ : (finitePlacePadicPrime place : ℕ) ≠ 2 →
      (∀ i : Fin 4,
        ¬(finitePlacePadicPrime place : ℕ) ∣ (![a, b, c, d] i).val) →
      ∃ q : Fin 4 → place.adicCompletion ℚ,
        (∃ i : Fin 4, q i ≠ 0) ∧
          (a.val : place.adicCompletion ℚ) * q 0 ^ 2 +
          (c.val : place.adicCompletion ℚ) * q 1 ^ 2 +
          (d.val : place.adicCompletion ℚ) * q 2 ^ 2 +
          ((2 * (a.val : ℚ) * t : ℚ) : place.adicCompletion ℚ) * q 3 ^ 2 = 0 := by
    intro hodd hgood
    have hgoodset : ∀ e ∈ ({a, b, c, d} : Finset CanonicalParts),
        ¬(finitePlacePadicPrime place : ℕ) ∣ e.val := by
      intro e he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl | rfl
      · simpa using hgood 0
      · simpa using hgood 1
      · simpa using hgood 2
      · simpa using hgood 3
    exact finiteCompletion_mixed_quadratic_nontrivial_zero_of_odd_good_prime
      place a b c d t hodd hgoodset ht hb
  exact mixedQuadratic_anisotropic_localCount_zero_ordered
    place a b c d t M A hM hmixed hb hQ hgoodQ h16 ha16 hoddTargets

/-- Every exceptional canonical tuple is eliminated, independently of the
ordering in which its mixed fourth-power condition is witnessed. -/
theorem exceptionalTuple_localCount_zero
    (d : Fin 4 → CanonicalParts) (hexceptional : ExceptionalTuple d)
    (M A : ℕ) (hM : M ≠ 0)
    (h16 : 16 ∣ M) (ha16 : A % 16 = 8)
    (hoddTargets : ∀ p : ℕ, p.Prime → p ≠ 2 →
      (∃ i : Fin 4, p ∣ (d i).val) →
      p ^ 2 ∣ M ∧ A % (p ^ 2) = p) :
    @localCount (fun i => (d i).val) M A ⟨hM⟩ = 0 := by
  rcases hexceptional with ⟨k, hk⟩ | ⟨σ, hmixed⟩
  · exact squareExceptional_localCount_zero
      d k hk M A hM h16 ha16 hoddTargets
  · have htargets' : ∀ p : ℕ, p.Prime → p ≠ 2 →
        (∃ i : Fin 4,
          p ∣ (![d (σ 0), d (σ 1), d (σ 2), d (σ 3)] i).val) →
        p ^ 2 ∣ M ∧ A % (p ^ 2) = p := by
      intro p hp hodd ⟨i, hi⟩
      apply hoddTargets p hp hodd
      refine ⟨σ i, ?_⟩
      fin_cases i <;> simpa using hi
    have hzero := mixedExceptional_localCount_zero_ordered
      (d (σ 0)) (d (σ 1)) (d (σ 2)) (d (σ 3)) hmixed
      M A hM h16 ha16 htargets'
    have hcoeff :
        (fun i : Fin 4 => (![d (σ 0), d (σ 1), d (σ 2), d (σ 3)] i).val) =
          (fun i : Fin 4 => (d (σ i)).val) := by
      funext i
      fin_cases i <;> rfl
    letI : NeZero M := ⟨hM⟩
    change localCount (fun i => (d i).val) M A = 0
    rw [← localCount_perm (fun i => (d i).val) M A σ]
    rw [← hcoeff]
    exact hzero

end Erdos940.Quartic
