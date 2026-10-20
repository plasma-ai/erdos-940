import Erdos940.Quartic.GaussianRingEquivalence
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# Norms of degree-one Gaussian prime ideals

The quotient of the Gaussian integer ring by a prime ideal still contains
a square root of `-1`. Consequently, its finite residue field cannot have
cardinality `3` modulo `4`.
-/

open scoped NumberField
open IsDedekindDomain

namespace Erdos940.Quartic

private abbrev FourthField := CyclotomicField 4 ℚ

attribute [local instance] Ideal.Quotient.field

noncomputable local instance (P : HeightOneSpectrum (𝓞 FourthField)) :
    Fintype (𝓞 FourthField ⧸ P.asIdeal) :=
  Fintype.ofFinite _

theorem gaussian_prime_ideal_absNorm_mod_four_ne_three
    (P : HeightOneSpectrum (𝓞 FourthField)) :
    Ideal.absNorm P.asIdeal % 4 ≠ 3 := by
  let u : 𝓞 FourthField := gaussianFourthIntegerRingEquiv Zsqrtd.sqrtd
  have hu : u * u = -1 := by
    dsimp [u]
    rw [← map_mul]
    simpa using congrArg gaussianFourthIntegerRingEquiv
      (Zsqrtd.dmuld (d := (-1 : ℤ)))
  let v : 𝓞 FourthField ⧸ P.asIdeal := Ideal.Quotient.mk P.asIdeal u
  have hv : v * v = -1 := by
    simpa [v] using congrArg (Ideal.Quotient.mk P.asIdeal) hu
  have hs : IsSquare (-1 : 𝓞 FourthField ⧸ P.asIdeal) :=
    ⟨v, by simpa [pow_two] using hv.symm⟩
  have hmod := (FiniteField.isSquare_neg_one_iff).mp hs
  have hcard : Fintype.card (𝓞 FourthField ⧸ P.asIdeal) =
      Ideal.absNorm P.asIdeal := by
    rw [← Nat.card_eq_fintype_card, Ideal.absNorm_apply,
      Submodule.cardQuot_apply]
  rwa [hcard] at hmod

theorem gaussian_prime_ideal_absNorm_mod_four_eq_one
    (P : HeightOneSpectrum (𝓞 FourthField))
    (h2 : (Ideal.absNorm P.asIdeal).Coprime 4) :
    Ideal.absNorm P.asIdeal % 4 = 1 := by
  have hodd : Odd (Ideal.absNorm P.asIdeal) :=
    Nat.coprime_two_right.mp
      (Nat.Coprime.of_dvd_right (by norm_num : 2 ∣ 4) h2)
  have hne := gaussian_prime_ideal_absNorm_mod_four_ne_three P
  rcases hodd with ⟨k, hk⟩
  omega

end Erdos940.Quartic
