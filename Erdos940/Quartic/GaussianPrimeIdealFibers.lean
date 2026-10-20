import Erdos940.Quartic.EulerPrimeChebyshev
import Erdos940.Quartic.GaussianHeckeCharacters
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# Fibers of Gaussian prime ideals over rational primes

The degree-two fundamental identity bounds the number of prime ideals
over a rational prime. This file connects that identity to the norm/fiber
interfaces of `EulerPrimeChebyshev`.
-/

namespace Erdos940.Quartic

open NumberField IsDedekindDomain

/-- The rational prime under a nonzero prime ideal of the Gaussian integers. -/
noncomputable def gaussianBasePrime
    (P : HeightOneSpectrum (𝓞 GaussianField)) : Nat.Primes := by
  let p := P.asIdeal.under ℤ
  have hp0 : p ≠ ⊥ := Ideal.IsIntegral.under_ne_bot ℤ P.ne_bot
  have hp : Prime p := Ideal.prime_of_isPrime hp0 inferInstance
  exact ⟨Ideal.absNorm p, (Int.prime_absNorm p).2 hp⟩

theorem gaussianBasePrime_absNorm
    (P : HeightOneSpectrum (𝓞 GaussianField)) :
    (gaussianBasePrime P).val = Ideal.absNorm (P.asIdeal.under ℤ) := rfl

theorem gaussianBasePrime_under
    (P : HeightOneSpectrum (𝓞 GaussianField)) :
    Ideal.span {((gaussianBasePrime P).val : ℤ)} =
      P.asIdeal.under ℤ := by
  rw [gaussianBasePrime_absNorm]
  exact Int.ideal_span_absNorm_eq_self _

private def gaussianPrimeOver (p : Nat.Primes)
    (P : HeightOneSpectrum (𝓞 GaussianField))
    (hP : gaussianBasePrime P = p) :
    (Ideal.span {(p.val : ℤ)}).primesOver (𝓞 GaussianField) := by
  refine ⟨P.asIdeal, P.isPrime, ⟨?_⟩⟩
  simpa [hP] using gaussianBasePrime_under P

private theorem gaussianPrimeOver_injective (p : Nat.Primes)
    {P Q : HeightOneSpectrum (𝓞 GaussianField)}
    (hP : gaussianBasePrime P = p) (hQ : gaussianBasePrime Q = p)
    (h : gaussianPrimeOver p P hP = gaussianPrimeOver p Q hQ) :
    P = Q := by
  apply HeightOneSpectrum.asIdeal_injective
  exact congrArg Subtype.val h

private theorem gaussian_ring_rank_two :
    Module.finrank ℤ (𝓞 GaussianField) = 2 := by
  rw [NumberField.RingOfIntegers.rank]
  letI : NeZero (4 : ℕ) := ⟨by decide⟩
  letI : IsCyclotomicExtension {4} ℚ GaussianField :=
    CyclotomicField.isCyclotomicExtension 4 ℚ
  rw [IsCyclotomicExtension.Rat.finrank 4 GaussianField]
  decide

/-- Every Gaussian prime ideal has norm `p^f`, where `p` is its rational
prime below and `f` is its inertia degree. -/
theorem gaussianPrime_absNorm_pow_inertiaDeg
    (P : HeightOneSpectrum (𝓞 GaussianField)) :
    (gaussianBasePrime P).val ^ P.asIdeal.inertiaDeg ℤ =
      Ideal.absNorm P.asIdeal := by
  change (Ideal.absNorm (P.asIdeal.under ℤ)) ^ P.asIdeal.inertiaDeg ℤ = _
  exact Ideal.absNorm_pow_inertiaDeg
    (R := ℤ) (S := 𝓞 GaussianField)
    (p := P.asIdeal.under ℤ) (q := P.asIdeal)

noncomputable instance gaussian_primesOver_fintype (p : Nat.Primes) :
    Fintype ((Ideal.span {(p.val : ℤ)}).primesOver (𝓞 GaussianField)) :=
  (Algebra.QuasiFinite.finite_primesOver
    (Ideal.span {(p.val : ℤ)}) :
    Set.Finite ((Ideal.span {(p.val : ℤ)}).primesOver (𝓞 GaussianField))).fintype

private theorem gaussian_fundamental_identity (p : Nat.Primes) :
    ∑ q : (Ideal.span {(p.val : ℤ)}).primesOver (𝓞 GaussianField),
      q.val.ramificationIdx ℤ * q.val.inertiaDeg ℤ = 2 := by
  letI : (Ideal.span {(p.val : ℤ)}).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime
      (Int.prime_iff_natAbs_prime.mpr (by simpa using p.property))
  rw [Ideal.sum_ramification_inertia_eq_finrank]
  exact gaussian_ring_rank_two

private theorem gaussian_primesOver_card_le_two (p : Nat.Primes) :
    Fintype.card ((Ideal.span {(p.val : ℤ)}).primesOver
      (𝓞 GaussianField)) ≤ 2 := by
  classical
  have hweight (q : (Ideal.span {(p.val : ℤ)}).primesOver
      (𝓞 GaussianField)) :
      1 ≤ q.val.ramificationIdx ℤ * q.val.inertiaDeg ℤ := by
    have he : 0 < q.val.ramificationIdx ℤ :=
      Ideal.ramificationIdx_pos ℤ q.val
    have hf : 0 < q.val.inertiaDeg ℤ := Ideal.inertiaDeg_pos q.val ℤ
    exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Nat.mul_pos he hf))
  have hsum :
      (∑ q : (Ideal.span {(p.val : ℤ)}).primesOver
        (𝓞 GaussianField), (1 : ℕ)) ≤
      ∑ q : (Ideal.span {(p.val : ℤ)}).primesOver
        (𝓞 GaussianField),
        q.val.ramificationIdx ℤ * q.val.inertiaDeg ℤ := by
    apply Finset.sum_le_sum
    intro q _
    exact hweight q
  simpa [gaussian_fundamental_identity p] using hsum

/-- At most two Gaussian prime ideals lie over any rational prime. -/
theorem gaussianBasePrime_fiber_card_le_two
    (F : Finset (HeightOneSpectrum (𝓞 GaussianField)))
    (p : Nat.Primes) :
    (F.filter fun P => gaussianBasePrime P = p).card ≤ 2 := by
  classical
  let s := F.subtype (fun P => gaussianBasePrime P = p)
  let t : Finset ((Ideal.span {(p.val : ℤ)}).primesOver
      (𝓞 GaussianField)) := Finset.univ
  let f : s → t := fun P =>
    ⟨gaussianPrimeOver p P.val.val P.val.property, Finset.mem_univ _⟩
  have hf : Function.Injective f := by
    intro P Q h
    apply Subtype.ext
    apply Subtype.ext
    exact gaussianPrimeOver_injective p P.val.property Q.val.property
      (congrArg Subtype.val h)
  have hcard := Finset.card_le_card_of_injective hf
  simpa [s, t, Finset.card_subtype] using
    hcard.trans (gaussian_primesOver_card_le_two p)

private theorem gaussianPrime_inertiaDeg_le_two
    (P : HeightOneSpectrum (𝓞 GaussianField)) :
    P.asIdeal.inertiaDeg ℤ ≤ 2 := by
  let p := gaussianBasePrime P
  let q := gaussianPrimeOver p P rfl
  have hsum := gaussian_fundamental_identity p
  have hterm : q.val.ramificationIdx ℤ * q.val.inertiaDeg ℤ ≤ 2 := by
    calc
      _ ≤ ∑ r : (Ideal.span {(p.val : ℤ)}).primesOver
          (𝓞 GaussianField),
          r.val.ramificationIdx ℤ * r.val.inertiaDeg ℤ := by
        simpa using (Finset.single_le_sum
          (s := (Finset.univ : Finset
            ((Ideal.span {(p.val : ℤ)}).primesOver (𝓞 GaussianField))))
          (f := fun r => r.val.ramificationIdx ℤ * r.val.inertiaDeg ℤ)
          (fun r _ => Nat.zero_le _) (Finset.mem_univ q))
      _ = 2 := hsum
  have he : 0 < q.val.ramificationIdx ℤ :=
    Ideal.ramificationIdx_pos ℤ q.val
  have hf : q.val.inertiaDeg ℤ = P.asIdeal.inertiaDeg ℤ := rfl
  rw [hf] at hterm
  nlinarith

private theorem gaussianPrime_inertiaDeg_one_or_two
    (P : HeightOneSpectrum (𝓞 GaussianField)) :
    P.asIdeal.inertiaDeg ℤ = 1 ∨ P.asIdeal.inertiaDeg ℤ = 2 := by
  have hpos : 0 < P.asIdeal.inertiaDeg ℤ :=
    Ideal.inertiaDeg_pos P.asIdeal ℤ
  have hle := gaussianPrime_inertiaDeg_le_two P
  omega

/-- Degree one is the split or ramified case; degree two is inert. -/
noncomputable def gaussianDegreeOne
    (P : HeightOneSpectrum (𝓞 GaussianField)) : Prop :=
  P.asIdeal.inertiaDeg ℤ = 1

noncomputable instance : DecidablePred gaussianDegreeOne :=
  Classical.decPred _

private theorem gaussian_primesOver_card_le_one_of_inertia_two
    (p : Nat.Primes)
    (q : (Ideal.span {(p.val : ℤ)}).primesOver (𝓞 GaussianField))
    (hq : q.val.inertiaDeg ℤ = 2) :
    Fintype.card ((Ideal.span {(p.val : ℤ)}).primesOver
      (𝓞 GaussianField)) ≤ 1 := by
  classical
  let U := (Ideal.span {(p.val : ℤ)}).primesOver (𝓞 GaussianField)
  have hsum := gaussian_fundamental_identity p
  have hterm (r : U) :
      (if r = q then 2 else 1) ≤
        r.val.ramificationIdx ℤ * r.val.inertiaDeg ℤ := by
    have he : 0 < r.val.ramificationIdx ℤ :=
      Ideal.ramificationIdx_pos ℤ r.val
    have hf : 0 < r.val.inertiaDeg ℤ :=
      Ideal.inertiaDeg_pos r.val ℤ
    by_cases hr : r = q
    · subst r
      simp only [↓reduceIte, hq]
      omega
    · simp only [hr, ↓reduceIte]
      exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Nat.mul_pos he hf))
  have hle : (∑ r : U, if r = q then (2 : ℕ) else 1) ≤ 2 := by
    calc
      _ ≤ ∑ r : U,
          r.val.ramificationIdx ℤ * r.val.inertiaDeg ℤ := by
        apply Finset.sum_le_sum
        intro r _
        exact hterm r
      _ = 2 := hsum
  have hleft : (∑ r : U, if r = q then (2 : ℕ) else 1) =
      Fintype.card U + 1 := by
    have hOne : (∑ r : U, if r = q then (1 : ℕ) else 0) = 1 := by
      simp
    calc
      (∑ r : U, if r = q then (2 : ℕ) else 1) =
          ∑ r : U, ((1 : ℕ) + if r = q then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro r _
        split_ifs <;> omega
      _ = (∑ r : U, (1 : ℕ)) +
          (∑ r : U, if r = q then (1 : ℕ) else 0) := by
        rw [Finset.sum_add_distrib]
      _ = Fintype.card U + 1 := by simp only [hOne]; simp
  change Fintype.card U ≤ 1
  omega

/-- At most one degree-two Gaussian prime ideal lies over a fixed rational
prime. The fundamental identity already includes the ramified prime `2`,
so no exceptional-prime exclusion is needed for this bound. -/
theorem gaussianDegreeTwo_fiber_card_le_one
    (F : Finset (HeightOneSpectrum (𝓞 GaussianField)))
    (p : Nat.Primes) :
    ((F.filter fun P => ¬ gaussianDegreeOne P).filter
      fun P => gaussianBasePrime P = p).card ≤ 1 := by
  classical
  let s := (F.filter fun P => ¬ gaussianDegreeOne P).filter
    fun P => gaussianBasePrime P = p
  by_cases hs : s.Nonempty
  · obtain ⟨P, hP⟩ := hs
    have hbase : gaussianBasePrime P = p :=
      (Finset.mem_filter.mp hP).2
    have hdegree : P.asIdeal.inertiaDeg ℤ = 2 := by
      have hnot : ¬ gaussianDegreeOne P :=
        (Finset.mem_filter.mp (Finset.mem_filter.mp hP).1).2
      rcases gaussianPrime_inertiaDeg_one_or_two P with h | h
      · exact False.elim (hnot h)
      · exact h
    have hcard := gaussian_primesOver_card_le_one_of_inertia_two p
      (gaussianPrimeOver p P hbase) hdegree
    let t : Finset ((Ideal.span {(p.val : ℤ)}).primesOver
        (𝓞 GaussianField)) := Finset.univ
    let f : s → t := fun Q =>
      ⟨gaussianPrimeOver p Q.val
        (Finset.mem_filter.mp Q.property).2, Finset.mem_univ _⟩
    have hf : Function.Injective f := by
      intro Q R h
      apply Subtype.ext
      exact gaussianPrimeOver_injective p
        (Finset.mem_filter.mp Q.property).2
        (Finset.mem_filter.mp R.property).2
        (congrArg Subtype.val h)
    have hle := Finset.card_le_card_of_injective hf
    simpa [s, t] using hle.trans hcard
  · simp only [Finset.not_nonempty_iff_eq_empty] at hs
    change s.card ≤ 1
    rw [hs]
    simp

/-- The abstract degree-one/degree-two norm is exactly the absolute ideal
norm of a Gaussian prime. -/
theorem gaussianIdealNorm_eq_absNorm
    (P : HeightOneSpectrum (𝓞 GaussianField)) :
    gaussianIdealNorm gaussianBasePrime gaussianDegreeOne P =
      (Ideal.absNorm P.asIdeal : ℝ) := by
  have hnorm := gaussianPrime_absNorm_pow_inertiaDeg P
  rcases gaussianPrime_inertiaDeg_one_or_two P with h | h
  · have hreal := congrArg (fun n : ℕ => (n : ℝ)) hnorm
    simpa [gaussianIdealNorm, gaussianDegreeOne, h] using hreal
  · have hreal := congrArg (fun n : ℕ => (n : ℝ)) hnorm
    simpa [gaussianIdealNorm, gaussianDegreeOne, h] using hreal

private theorem gaussianDegreeOne_fiber_card_le_two
    (F : Finset (HeightOneSpectrum (𝓞 GaussianField)))
    (p : Nat.Primes) :
    ((F.filter gaussianDegreeOne).filter
      fun P => gaussianBasePrime P = p).card ≤ 2 := by
  have hsub : ((F.filter gaussianDegreeOne).filter
      fun P => gaussianBasePrime P = p) ⊆
        F.filter (fun P => gaussianBasePrime P = p) := by
    intro P hP
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hP).1).1,
       (Finset.mem_filter.mp hP).2⟩
  exact (Finset.card_le_card hsub).trans
    (gaussianBasePrime_fiber_card_le_two F p)

/-- Concrete Chebyshev-below estimate for Gaussian prime ideals, with the
actual absolute ideal norm. -/
theorem gaussianPrimeIdealLogSum_le
    (F : Finset (HeightOneSpectrum (𝓞 GaussianField)))
    (B : ℝ) (hB : 2 ≤ B)
    (hbelow : ∀ P ∈ F, (Ideal.absNorm P.asIdeal : ℝ) ≤ B) :
    (∑ P ∈ F,
      Real.log (Ideal.absNorm P.asIdeal : ℝ) /
        (Ideal.absNorm P.asIdeal : ℝ)) ≤
      (6 * Real.log 4 * (1 + 1 / Real.log 2)) * Real.log B := by
  have h := gaussianIdealLogSum_le F gaussianBasePrime gaussianDegreeOne
    B hB
    (by intro P hP; rw [gaussianIdealNorm_eq_absNorm]; exact hbelow P hP)
    (gaussianDegreeOne_fiber_card_le_two F)
    (gaussianDegreeTwo_fiber_card_le_one F)
  convert h using 1
  apply Finset.sum_congr rfl
  intro P _
  rw [gaussianIdealNorm_eq_absNorm]

/-- Concrete finite smoothed-tail estimate, again in absolute ideal norms. -/
theorem gaussianPrimeIdealFiniteSmoothedTail_le
    (F : Finset (HeightOneSpectrum (𝓞 GaussianField)))
    (B : ℝ) (hB : 2 ≤ B)
    (habove : ∀ P ∈ F, gaussianDegreeOne P →
      B < (Ideal.absNorm P.asIdeal : ℝ)) :
    (∑ P ∈ F,
      eulerMassTerm (fun P => (Ideal.absNorm P.asIdeal : ℝ)) B P) ≤
      2 * (Real.log 4 * (1 + 2 / Real.log 2)) +
        reciprocalSquareConstant := by
  have h := gaussianFiniteSmoothedTail_le F gaussianBasePrime
    gaussianDegreeOne B hB
    (by
      intro P hP hd
      have heq : (gaussianBasePrime P : ℝ) =
          (Ideal.absNorm P.asIdeal : ℝ) := by
        simpa [gaussianIdealNorm, hd] using
          gaussianIdealNorm_eq_absNorm P
      rw [heq]
      exact habove P hP hd)
    (gaussianDegreeOne_fiber_card_le_two F)
    (gaussianDegreeTwo_fiber_card_le_one F)
  convert h using 1
  apply Finset.sum_congr rfl
  intro P _
  simp only [eulerMassTerm]
  rw [gaussianIdealNorm_eq_absNorm]

/-- The concrete infinite tail estimate needed to compare a Gaussian
prime-ideal Euler sum with its logarithm. -/
theorem gaussianPrimeIdealTailMass_le
    (S : Finset (HeightOneSpectrum (𝓞 GaussianField)))
    (B : ℝ) (hB : 2 ≤ B)
    (hS : ∀ P : (Sᶜ : Set (HeightOneSpectrum (𝓞 GaussianField))),
      B < (Ideal.absNorm P.val.asIdeal : ℝ)) :
    (∑' P : (Sᶜ : Set (HeightOneSpectrum (𝓞 GaussianField))),
      eulerMassTerm
        (fun P : HeightOneSpectrum (𝓞 GaussianField) =>
          (Ideal.absNorm P.asIdeal : ℝ)) B P.val) ≤
      2 * (Real.log 4 * (1 + 2 / Real.log 2)) +
        reciprocalSquareConstant := by
  classical
  apply Real.tsum_le_of_sum_le (fun P => by
    unfold eulerMassTerm
    positivity)
  intro u
  let f : (Sᶜ : Set (HeightOneSpectrum (𝓞 GaussianField))) →
      HeightOneSpectrum (𝓞 GaussianField) := Subtype.val
  have hf : Function.Injective f := Subtype.val_injective
  have hF : ∀ P ∈ u.image f, gaussianDegreeOne P →
      B < (Ideal.absNorm P.asIdeal : ℝ) := by
    intro P hP _
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hP
    exact hS Q
  calc
    (∑ P ∈ u, eulerMassTerm
      (fun P : HeightOneSpectrum (𝓞 GaussianField) =>
        (Ideal.absNorm P.asIdeal : ℝ)) B P.val) =
      ∑ P ∈ u.image f,
        eulerMassTerm
          (fun P : HeightOneSpectrum (𝓞 GaussianField) =>
            (Ideal.absNorm P.asIdeal : ℝ)) B P := by
      rw [Finset.sum_image (fun P _ Q _ h => hf h)]
    _ ≤ 2 * (Real.log 4 * (1 + 2 / Real.log 2)) +
        reciprocalSquareConstant :=
      gaussianPrimeIdealFiniteSmoothedTail_le (u.image f) B hB hF

/-- The same finite-tail estimate supplies summability of the unsigned
Gaussian prime-ideal tail, as required by the Euler-log comparison. -/
theorem gaussianPrimeIdealTailMass_summable
    (S : Finset (HeightOneSpectrum (𝓞 GaussianField)))
    (B : ℝ) (hB : 2 ≤ B)
    (hS : ∀ P : (Sᶜ : Set (HeightOneSpectrum (𝓞 GaussianField))),
      B < (Ideal.absNorm P.val.asIdeal : ℝ)) :
    Summable (fun P : (Sᶜ : Set (HeightOneSpectrum (𝓞 GaussianField))) =>
      eulerMassTerm
        (fun P : HeightOneSpectrum (𝓞 GaussianField) =>
          (Ideal.absNorm P.asIdeal : ℝ)) B P.val) := by
  classical
  refine summable_of_sum_le
    (c := 2 * (Real.log 4 * (1 + 2 / Real.log 2)) +
      reciprocalSquareConstant)
    (fun P => by unfold eulerMassTerm; positivity) ?_
  intro u
  let f : (Sᶜ : Set (HeightOneSpectrum (𝓞 GaussianField))) →
      HeightOneSpectrum (𝓞 GaussianField) := Subtype.val
  have hf : Function.Injective f := Subtype.val_injective
  have hF : ∀ P ∈ u.image f, gaussianDegreeOne P →
      B < (Ideal.absNorm P.asIdeal : ℝ) := by
    intro P hP _
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hP
    exact hS Q
  calc
    (∑ P ∈ u, eulerMassTerm
      (fun P : HeightOneSpectrum (𝓞 GaussianField) =>
        (Ideal.absNorm P.asIdeal : ℝ)) B P.val) =
      ∑ P ∈ u.image f,
        eulerMassTerm
          (fun P : HeightOneSpectrum (𝓞 GaussianField) =>
            (Ideal.absNorm P.asIdeal : ℝ)) B P := by
      rw [Finset.sum_image (fun P _ Q _ h => hf h)]
    _ ≤ 2 * (Real.log 4 * (1 + 2 / Real.log 2)) +
        reciprocalSquareConstant :=
      gaussianPrimeIdealFiniteSmoothedTail_le (u.image f) B hB hF

end Erdos940.Quartic
