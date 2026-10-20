import Erdos940.Quartic.CanonicalParts
import Erdos940.Quartic.LocalQuadraticPerturbation

/-!
# Nonsingular quartic zero over an odd rational finite completion

An integral quartic value divisible by `p`, with one coefficient and
coordinate both nonzero modulo `p`, lifts to a nonzero `p`-adic zero.
-/

open scoped NumberField
open NumberField IsDedekindDomain

namespace Erdos940.Quartic

/-- The scalar Hensel step, with its derivative-unit condition exposed. -/
theorem padicInt_quartic_hensel_unit
    (p a b x : ℕ) [Fact p.Prime]
    (hval : p ∣ a * x ^ 4 + b)
    (hderivUnit : ¬p ∣ 4 * a * x ^ 3) :
    ∃ y : ℤ_[p], y ≠ 0 ∧ (a : ℤ_[p]) * y ^ 4 + (b : ℤ_[p]) = 0 := by
  let F : Polynomial ℤ_[p] :=
    Polynomial.C (a : ℤ_[p]) * Polynomial.X ^ 4 + Polynomial.C (b : ℤ_[p])
  have heval : F.aeval (x : ℤ_[p]) = ((a * x ^ 4 + b : ℕ) : ℤ_[p]) := by
    simp [F]
  have hderiv : F.derivative.aeval (x : ℤ_[p]) =
      ((4 * a * x ^ 3 : ℕ) : ℤ_[p]) := by
    simp [F]
    ring
  have hderivNorm : ‖F.derivative.aeval (x : ℤ_[p])‖ = 1 := by
    rw [hderiv]
    exact PadicInt.norm_natCast_eq_one_iff.mpr
      ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hderivUnit)
  obtain ⟨k, hk⟩ := hval
  have hvalNorm : ‖F.aeval (x : ℤ_[p])‖ < 1 := by
    rw [heval, hk, Nat.cast_mul, norm_mul]
    calc
      ‖(p : ℤ_[p])‖ * ‖(k : ℤ_[p])‖ ≤ ‖(p : ℤ_[p])‖ * 1 :=
        mul_le_mul_of_nonneg_left (PadicInt.norm_le_one _) (norm_nonneg _)
      _ = ‖(p : ℤ_[p])‖ := mul_one _
      _ < 1 := PadicInt.norm_natCast_lt_one_iff.mpr dvd_rfl
  have hbound : ‖F.aeval (x : ℤ_[p])‖ <
      ‖F.derivative.aeval (x : ℤ_[p])‖ ^ 2 := by
    rw [hderivNorm]
    simpa using hvalNorm
  obtain ⟨y, hy, _, hyDeriv, _⟩ := hensels_lemma (F := F) (a := (x : ℤ_[p])) hbound
  have hy0 : y ≠ 0 := by
    intro h
    have hd0 : F.derivative.aeval y = 0 := by simp [F, h]
    rw [hd0, norm_zero, hderivNorm] at hyDeriv
    exact zero_ne_one hyDeriv
  refine ⟨y, hy0, ?_⟩
  simpa [F] using hy

/-- A nonsingular integral zero of a diagonal quartic form lifts over `ℚ_p`. -/
theorem padic_quartic_hensel_fin4
    (p : ℕ) [Fact p.Prime]
    (d x : Fin 4 → ℕ) (i : Fin 4)
    (hodd : p ≠ 2)
    (hval : p ∣ ∑ j : Fin 4, d j * x j ^ 4)
    (hdi : ¬p ∣ d i) (hxi : ¬p ∣ x i) :
    ∃ y : Fin 4 → ℚ_[p], y i ≠ 0 ∧
      (∑ j : Fin 4, (d j : ℚ_[p]) * y j ^ 4) = 0 := by
  classical
  have hp : p.Prime := Fact.out
  have hfour : ¬p ∣ 4 := by
    intro h
    have hpow : p ∣ 2 ^ 2 := by simpa only [show (2 : ℕ) ^ 2 = 4 by norm_num] using h
    have htwo : p ∣ 2 := hp.dvd_of_dvd_pow hpow
    exact hodd ((Nat.dvd_prime_two_le (by decide : Nat.Prime 2) hp.two_le).mp htwo)
  have hderivUnit : ¬p ∣ 4 * d i * x i ^ 3 := by
    intro h
    rcases hp.dvd_mul.mp h with hleft | hright
    · rcases hp.dvd_mul.mp hleft with h4 | hd
      · exact hfour h4
      · exact hdi hd
    · exact hxi (hp.dvd_of_dvd_pow hright)
  let B : ℕ := ∑ j ∈ (Finset.univ : Finset (Fin 4)).erase i, d j * x j ^ 4
  have hsplit : d i * x i ^ 4 + B = ∑ j : Fin 4, d j * x j ^ 4 := by
    simpa only [B] using
      (Finset.add_sum_erase (Finset.univ : Finset (Fin 4))
        (fun j : Fin 4 => d j * x j ^ 4) (Finset.mem_univ i))
  have hscalar : p ∣ d i * x i ^ 4 + B := by rw [hsplit]; exact hval
  obtain ⟨Y, hY0, hYroot⟩ := padicInt_quartic_hensel_unit
    p (d i) B (x i) hscalar hderivUnit
  have hYroot' : (d i : ℚ_[p]) * (Y : ℚ_[p]) ^ 4 + (B : ℚ_[p]) = 0 := by
    simpa using congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) hYroot
  let y : Fin 4 → ℚ_[p] := Function.update (fun j => (x j : ℚ_[p])) i (Y : ℚ_[p])
  have hyi : y i ≠ 0 := by
    simpa [y] using (PadicInt.coe_ne_zero.mpr hY0)
  refine ⟨y, hyi, ?_⟩
  have hupdate : (fun j : Fin 4 => (d j : ℚ_[p]) * y j ^ 4) =
      Function.update (fun j : Fin 4 => (d j : ℚ_[p]) * (x j : ℚ_[p]) ^ 4)
        i ((d i : ℚ_[p]) * (Y : ℚ_[p]) ^ 4) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [y, Function.update_self]
    · simp [y, Function.update_of_ne hji]
  rw [hupdate, Finset.sum_update_of_mem (Finset.mem_univ i)]
  simpa [B, Finset.erase_eq] using hYroot'

local instance finitePlacePadicPrimeFactForQuarticHensel
    (place : HeightOneSpectrum (𝓞 ℚ)) :
    Fact (Nat.Prime (finitePlacePadicPrime place : ℕ)) :=
  ⟨(finitePlacePadicPrime place).2⟩

/-- A nonsingular zero modulo an odd prime gives a nonzero quartic zero in
the corresponding rational finite completion. -/
theorem finiteCompletion_quartic_hensel_fin4
    (place : HeightOneSpectrum (𝓞 ℚ))
    (d : Fin 4 → CanonicalParts) (x : Fin 4 → ℕ) (i : Fin 4)
    (hodd : (finitePlacePadicPrime place : ℕ) ≠ 2)
    (hval : (finitePlacePadicPrime place : ℕ) ∣
      ∑ j : Fin 4, (d j).val * x j ^ 4)
    (hdi : ¬(finitePlacePadicPrime place : ℕ) ∣ (d i).val)
    (hxi : ¬(finitePlacePadicPrime place : ℕ) ∣ x i) :
    ∃ y : Fin 4 → place.adicCompletion ℚ, y i ≠ 0 ∧
      (∑ j : Fin 4,
        ((d j).val : place.adicCompletion ℚ) * y j ^ 4) = 0 := by
  classical
  let p := finitePlacePadicPrime place
  let e := finitePlacePadicEquiv place
  obtain ⟨z, hzi, hz⟩ := padic_quartic_hensel_fin4 p.1
    (fun j => (d j).val) x i hodd hval hdi hxi
  let y : Fin 4 → place.adicCompletion ℚ := fun j => e.symm (z j)
  have hyi : y i ≠ 0 := by
    intro hy
    apply hzi
    have heq := congrArg e hy
    simpa [y] using heq
  refine ⟨y, hyi, ?_⟩
  apply e.injective
  simpa [y] using hz

/-- The target residue `p` modulo `p²` gives the divisibility hypothesis
for the nonsingular quartic Hensel lift. -/
theorem finiteCompletion_quartic_hensel_of_prime_square_target
    (place : HeightOneSpectrum (𝓞 ℚ))
    (d : Fin 4 → CanonicalParts) (x : Fin 4 → ℕ) (i : Fin 4)
    (hodd : (finitePlacePadicPrime place : ℕ) ≠ 2)
    (hval : (∑ j : Fin 4, (d j).val * x j ^ 4) %
      (finitePlacePadicPrime place : ℕ) ^ 2 =
        (finitePlacePadicPrime place : ℕ))
    (hdi : ¬(finitePlacePadicPrime place : ℕ) ∣ (d i).val)
    (hxi : ¬(finitePlacePadicPrime place : ℕ) ∣ x i) :
    ∃ y : Fin 4 → place.adicCompletion ℚ, y i ≠ 0 ∧
      (∑ j : Fin 4,
        ((d j).val : place.adicCompletion ℚ) * y j ^ 4) = 0 := by
  let p : ℕ := finitePlacePadicPrime place
  have hpp : p ∣ p ^ 2 := by
    use p
    ring
  have hmod : (∑ j : Fin 4, (d j).val * x j ^ 4) % p = 0 := by
    calc
      (∑ j : Fin 4, (d j).val * x j ^ 4) % p =
          ((∑ j : Fin 4, (d j).val * x j ^ 4) % (p ^ 2)) % p :=
        (Nat.mod_mod_of_dvd _ hpp).symm
      _ = p % p := congrArg (fun k : ℕ => k % p) hval
      _ = 0 := Nat.mod_self p
  exact finiteCompletion_quartic_hensel_fin4 place d x i hodd
    (Nat.dvd_of_mod_eq_zero hmod) hdi hxi

end Erdos940.Quartic
