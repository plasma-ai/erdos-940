import Erdos940.Quartic.InertLocalTrace
import Mathlib.Basic.Real.Basic

/-!
# Intrinsic quartic local trace

The prime-field count determines its trace coefficient uniquely. This
definition is independent of whether the prime splits in `ℤ[i]` and avoids
choosing a quartic character in the final sieve statement.
-/

namespace Erdos940.Quartic

noncomputable def quarticIntrinsicTrace (p : ℕ) [NeZero p]
    (a : Fin 4 → ZMod p) : ℝ :=
  ((Nat.card {x : Fin 4 → ZMod p // ∑ i, a i * x i ^ 4 = 0} : ℝ) -
    (p : ℝ) ^ 3) / (((p : ℝ) - 1) * (p : ℝ))

theorem quarticIntrinsicTrace_local_density
    (p : ℕ) [NeZero p] (hp : 1 < p) (a : Fin 4 → ZMod p) :
    (Nat.card {x : Fin 4 → ZMod p // ∑ i, a i * x i ^ 4 = 0} : ℝ) /
        (p : ℝ) ^ 3 =
      1 + quarticIntrinsicTrace p a *
        ((p : ℝ)⁻¹ - ((p : ℝ) ^ 2)⁻¹) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have hpr : (1 : ℝ) < p := by exact_mod_cast hp
    linarith
  unfold quarticIntrinsicTrace
  field_simp
  ring

/-- Uniqueness of the trace coefficient for a prime-field local density. -/
theorem quarticIntrinsicTrace_eq_of_local_density
    (p : ℕ) [NeZero p] (hp : 1 < p) (a : Fin 4 → ZMod p)
    (A : ℝ)
    (hlocal :
      (Nat.card {x : Fin 4 → ZMod p // ∑ i, a i * x i ^ 4 = 0} : ℝ) /
          (p : ℝ) ^ 3 =
        1 + A * ((p : ℝ)⁻¹ - ((p : ℝ) ^ 2)⁻¹)) :
    quarticIntrinsicTrace p a = A := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have hpr : (1 : ℝ) < p := by exact_mod_cast hp
    linarith
  unfold quarticIntrinsicTrace
  field_simp at hlocal ⊢
  nlinarith [hlocal]

/-- At inert primes the intrinsic trace is the ordinary quadratic
character of the product of the four coefficients. -/
theorem quarticIntrinsicTrace_eq_quadraticChar_of_inert
    (p : ℕ) [Fact p.Prime] (hmod : p % 4 = 3)
    (a : Fin 4 → ZMod p) (ha : ∀ i, a i ≠ 0) :
    quarticIntrinsicTrace p a =
      (quadraticChar (ZMod p) (∏ i, a i) : ℝ) := by
  classical
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hc := inert_quartic_zero_count hmod a ha
  have hcard : Nat.card {x : Fin 4 → ZMod p // ∑ i, a i * x i ^ 4 = 0} =
      localQuarticCount (ZMod p) 0 a := by
    simp only [localQuarticCount, ← Nat.card_eq_fintype_card]
  have hcR :
      (Nat.card {x : Fin 4 → ZMod p // ∑ i, a i * x i ^ 4 = 0} : ℝ) =
        (p : ℝ) ^ 3 + ((p : ℝ) - 1) * (p : ℝ) *
          (quadraticChar (ZMod p) (∏ i, a i) : ℝ) := by
    rw [hcard]
    exact
      (by exact_mod_cast hc :
        (localQuarticCount (ZMod p) 0 a : ℝ) =
          (p : ℝ) ^ 3 + ((p : ℝ) - 1) * (p : ℝ) *
            (quadraticChar (ZMod p) (∏ i, a i) : ℝ))
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hlocal :
      (Nat.card {x : Fin 4 → ZMod p // ∑ i, a i * x i ^ 4 = 0} : ℝ) /
          (p : ℝ) ^ 3 =
        1 + (quadraticChar (ZMod p) (∏ i, a i) : ℝ) *
          ((p : ℝ)⁻¹ - ((p : ℝ) ^ 2)⁻¹) := by
    rw [hcR]
    field_simp
  exact quarticIntrinsicTrace_eq_of_local_density p hp a _ hlocal

theorem quarticIntrinsicTrace_abs_le_one_of_inert
    (p : ℕ) [Fact p.Prime] (hmod : p % 4 = 3)
    (a : Fin 4 → ZMod p) (ha : ∀ i, a i ≠ 0) :
    |quarticIntrinsicTrace p a| ≤ 1 := by
  rw [quarticIntrinsicTrace_eq_quadraticChar_of_inert p hmod a ha]
  have hprod : (∏ i, a i) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (by
      intro i _
      exact ha i)
  rcases quadraticChar_dichotomy hprod with h | h
  · rw [h]
    norm_num
  · rw [h]
    norm_num

end Erdos940.Quartic
