import Erdos940.Quartic.QuadraticZeroCount
import Erdos940.Quartic.LocalPerturbationCongruence

/-!
# Lifting a nonsingular quadratic zero at an odd finite place

A nonzero zero of a four-variable diagonal quadratic form modulo `p` has a
nonzero coordinate. When all coefficients are units modulo `p`, the value at
integer representatives lies in `pℤ_p` while that coordinate contributes a
unit. The existing quadratic perturbation lemma removes this small value.
-/

open scoped NumberField
open NumberField IsDedekindDomain

namespace Erdos940.Quartic

/-- At an odd finite place where all four coefficients are units, the
diagonal quaternary quadratic form has a nontrivial zero. -/
theorem finiteCompletion_quadratic_nontrivial_zero_of_odd_good_prime
    (place : HeightOneSpectrum (𝓞 ℚ))
    (hodd : (finitePlacePadicPrime place : ℕ) ≠ 2)
    (a : Fin 4 → ℕ)
    (ha : ∀ i, ¬(finitePlacePadicPrime place : ℕ) ∣ a i) :
    ∃ y : Fin 4 → place.adicCompletion ℚ,
      (∃ i, y i ≠ 0) ∧
        (∑ i : Fin 4, (a i : place.adicCompletion ℚ) * y i ^ 2) = 0 := by
  classical
  let p : ℕ := finitePlacePadicPrime place
  have hp : p.Prime := (finitePlacePadicPrime place).2
  letI : Fact p.Prime := ⟨hp⟩
  have hac (i : Fin 4) : (a i : ZMod p) ≠ 0 := by
    intro hz
    exact ha i ((ZMod.natCast_eq_zero_iff _ _).mp hz)
  obtain ⟨x, hxzero, hxnon⟩ :=
    zmod_quadratic_four_nontrivial_zero (q := p) hodd
      (fun i => (a i : ZMod p)) hac
  obtain ⟨i, hxi⟩ : ∃ i : Fin 4, x i ≠ 0 := by
    by_contra h
    push Not at h
    apply hxnon
    funext j
    exact h j
  let z : Fin 4 → ℕ := fun j => (x j).val
  let N : ℕ := ∑ j : Fin 4, a j * z j ^ 2
  have hcast : (N : ZMod p) = 0 := by
    dsimp [N]
    push_cast
    simpa only [z, ZMod.natCast_zmod_val] using hxzero
  have hN : p ∣ N := (ZMod.natCast_eq_zero_iff _ _).mp hcast
  have hzi : ¬p ∣ z i := by
    intro hd
    have hz : (z i : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
    exact hxi (by simpa only [z, ZMod.natCast_zmod_val] using hz)
  have hU : ¬p ∣ a i * z i ^ 2 := by
    intro hdiv
    rcases hp.dvd_mul.mp hdiv with hleft | hright
    · exact ha i hleft
    · exact hzi (hp.dvd_of_dvd_pow hright)
  have hU0 : a i * z i ^ 2 ≠ 0 := by
    intro hz
    exact hU (by rw [hz]; exact dvd_zero p)
  let aa : Fin 4 → place.adicCompletion ℚ := fun j => (a j : place.adicCompletion ℚ)
  let zz : Fin 4 → place.adicCompletion ℚ := fun j => (z j : place.adicCompletion ℚ)
  have hvalue : (∑ j : Fin 4, aa j * zz j ^ 2) =
      (N : place.adicCompletion ℚ) := by
    simp [aa, zz, N]
  have hterm : aa i * zz i ^ 2 ≠ 0 := by
    have hcastU : ((a i * z i ^ 2 : ℕ) : place.adicCompletion ℚ) ≠ 0 := by
      have hq : ((a i * z i ^ 2 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hU0
      simpa only [map_natCast, map_zero] using
        (algebraMap ℚ (place.adicCompletion ℚ)).injective.ne hq
    simpa [aa, zz, Nat.cast_mul, Nat.cast_pow] using hcastU
  have hsmall : finiteCompletionPerturbationSmall place
      ((N : place.adicCompletion ℚ) / (aa i * zz i ^ 2)) := by
    have hs := finiteCompletion_small_of_odd_nat_dvd_unit place N (a i * z i ^ 2)
      hodd hN hU
    simpa only [aa, zz, Nat.cast_mul, Nat.cast_pow] using hs
  obtain ⟨y, hy, hzero⟩ := finiteCompletion_diagonal_quadratic_perturb_fin4
    place aa zz i (N : place.adicCompletion ℚ) hvalue hterm hsmall
  exact ⟨y, ⟨i, hy⟩, hzero⟩

end Erdos940.Quartic
