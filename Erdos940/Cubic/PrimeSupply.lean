module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import CebotarevDensity.Main

/-!
# Primes for the cube-full sum argument

The prime-supply step in Beyer and de Ryke, Lemma 5.1 and the proof of
Theorem 1.1, concerns a finite set `D` of positive fourth-full parts. It
requires primes `q ≡ 1 (mod 3)` at which every `d ∈ D` is a nonzero cube,
with a divergent reciprocal sum.

The proof of `goodPrimeWeights_diverge` uses the splitting field of
`(X² + X + 1) * ∏ d ∈ D, (X³ - d)` and the Chebotarev theorem.
Integral roots are reduced at completely split primes; prime-ideal density
is then transferred to a reciprocal sum over rational primes. The finite-
selection result follows from divergence by stopping at the first partial
sum to reach the requested size.
-/

@[expose] public section

namespace Erdos940

open Filter NumberField Topology
open scoped Classical

/-- The polynomial whose splitting field is used in Beyer and de Ryke,
Lemma 5.1. Its first factor adjoins a primitive cube root of unity; the
remaining factors adjoin cube roots of the elements of `D`. -/
noncomputable def cubeSplitPolynomial (D : Finset ℕ) : Polynomial ℚ :=
  (Polynomial.X ^ 2 + Polynomial.X + 1) *
    D.prod (fun d => Polynomial.X ^ 3 - Polynomial.C (d : ℚ))

/-- The number field used for a fixed finite set of fourth-full parts. -/
abbrev CubeSplitField (D : Finset ℕ) := (cubeSplitPolynomial D).SplittingField

private instance (D : Finset ℕ) : NumberField (CubeSplitField D) := by
  letI : FiniteDimensional ℚ (CubeSplitField D) :=
    Polynomial.IsSplittingField.finiteDimensional (CubeSplitField D) (cubeSplitPolynomial D)
  exact NumberField.of_module_finite ℚ (CubeSplitField D)

private instance (D : Finset ℕ) : IsGalois ℚ (CubeSplitField D) := by
  haveI : Algebra.IsSeparable ℚ (CubeSplitField D) := inferInstance
  exact isGalois_iff.mpr
    ⟨inferInstance, Normal.of_isSplittingField (cubeSplitPolynomial D)⟩

/-- The local conditions supplied by the splitting-field argument. -/
def GoodPrime (D : Finset ℕ) (q : ℕ) : Prop :=
  q.Prime ∧ q % 3 = 1 ∧
    ∀ d ∈ D, ∃ x : ZMod q, x ≠ 0 ∧ x ^ 3 = (d : ZMod q)

private theorem cubeSplitPolynomial_monic (D : Finset ℕ) :
    (cubeSplitPolynomial D).Monic := by
  unfold cubeSplitPolynomial
  rw [← Polynomial.cyclotomic_three ℚ]
  exact (Polynomial.cyclotomic.monic 3 ℚ).mul
    (Polynomial.monic_prod_of_monic D _ (fun d _ =>
      Polynomial.monic_X_pow_sub_C (d : ℚ) (by decide)))

/-- Each cubic factor has an integral root in a field where the defining
polynomial splits. This is the root that is later reduced modulo a prime of
the ring of integers. -/
private theorem exists_integral_cubic_root_of_splits
    (D : Finset ℕ) (L : Type*) [Field L] [NumberField L]
    [Algebra ℚ L]
    (hpoly : ((cubeSplitPolynomial D).map (algebraMap ℚ L)).Splits)
    (d : ℕ) (hd : d ∈ D) :
    ∃ x : 𝓞 L, (x : L) ^ 3 = (d : L) := by
  have hne : (cubeSplitPolynomial D).map (algebraMap ℚ L) ≠ 0 :=
    ((cubeSplitPolynomial_monic D).map (algebraMap ℚ L)).ne_zero
  have hdiv : (Polynomial.X ^ 3 - Polynomial.C (d : ℚ)) ∣
      cubeSplitPolynomial D := by
    unfold cubeSplitPolynomial
    exact dvd_mul_of_dvd_right
      (Finset.dvd_prod_of_mem
        (fun e : ℕ => (Polynomial.X : Polynomial ℚ) ^ 3 - Polynomial.C (e : ℚ)) hd) _
  have hsplit : ((Polynomial.X ^ 3 - Polynomial.C (d : ℚ)).map
      (algebraMap ℚ L)).Splits :=
    hpoly.of_dvd hne (Polynomial.map_dvd (algebraMap ℚ L) hdiv)
  have hdegree : Polynomial.degree
      ((Polynomial.X ^ 3 - Polynomial.C (d : ℚ)).map (algebraMap ℚ L)) ≠ 0 := by
    have heq : (Polynomial.X ^ 3 - Polynomial.C (d : ℚ)).map (algebraMap ℚ L) =
        (Polynomial.X : Polynomial L) ^ 3 - Polynomial.C (d : L) := by simp
    rw [heq, Polynomial.degree_X_pow_sub_C (by decide)]
    norm_num
  obtain ⟨x, hx⟩ := hsplit.exists_eval_eq_zero hdegree
  have hxpow : x ^ 3 = (d : L) := by
    exact sub_eq_zero.mp (by simpa using hx)
  have hxint : IsIntegral ℤ x :=
    IsIntegral.of_pow (n := 3) (by decide) (by
      rw [hxpow]
      simpa only [map_natCast] using
        (isIntegral_algebraMap (R := ℤ) (A := L) (x := (d : ℤ))))
  exact ⟨⟨x, hxint⟩, hxpow⟩

/-- The cyclotomic factor has an integral root in the splitting field. -/
private theorem exists_integral_cyclotomic_root_of_splits
    (D : Finset ℕ) (L : Type*) [Field L] [NumberField L]
    [Algebra ℚ L]
    (hpoly : ((cubeSplitPolynomial D).map (algebraMap ℚ L)).Splits) :
    ∃ z : 𝓞 L, (z : L) ^ 2 + (z : L) + 1 = 0 := by
  have hne : (cubeSplitPolynomial D).map (algebraMap ℚ L) ≠ 0 :=
    ((cubeSplitPolynomial_monic D).map (algebraMap ℚ L)).ne_zero
  have hdiv : (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial ℚ) ∣
      cubeSplitPolynomial D := by
    unfold cubeSplitPolynomial
    exact ⟨_, rfl⟩
  have hsplit : ((Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial ℚ).map
      (algebraMap ℚ L)).Splits :=
    hpoly.of_dvd hne (Polynomial.map_dvd (algebraMap ℚ L) hdiv)
  have hcycl : (Polynomial.cyclotomic 3 L).Splits := by
    simpa only [← Polynomial.cyclotomic_three ℚ, Polynomial.map_cyclotomic] using hsplit
  obtain ⟨z, hz⟩ := hcycl.exists_eval_eq_zero
    (ne_of_gt (Polynomial.degree_cyclotomic_pos 3 L (by decide)))
  have hzroot : (Polynomial.cyclotomic 3 L).IsRoot z := hz
  have hzprim : IsPrimitiveRoot z 3 :=
    (Polynomial.isRoot_cyclotomic_iff_charZero (by decide)).mp hzroot
  have hzint : IsIntegral ℤ z := hzprim.isIntegral (by decide)
  refine ⟨⟨z, hzint⟩, ?_⟩
  change z ^ 2 + z + 1 = 0
  simpa [Polynomial.IsRoot, Polynomial.cyclotomic_three] using hzroot

/- Rational-prime ideal dictionary: Chris Birkbeck, AINTLIB,
   CebotarevDensity/Main.lean (Apache 2.0). -/

private theorem absNorm_span_nat (q : ℕ) :
    Ideal.absNorm (Ideal.span {(q : 𝓞 ℚ)}) = q := by
  rw [Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank,
    Module.finrank_self, pow_one]

private theorem ratSpan_eq_comap_intSpan (q : ℕ) :
    Ideal.span {(q : 𝓞 ℚ)} =
      Ideal.comap Rat.ringOfIntegersEquiv (Ideal.span {(q : ℤ)}) := by
  rw [← Ideal.map_symm Rat.ringOfIntegersEquiv, Ideal.map_span, Set.image_singleton]
  congr 2
  simp [map_natCast]

private theorem ratPrime_eq_span (𝔭 : Ideal (𝓞 ℚ))
    (hp : 𝔭.IsPrime) (hne : 𝔭 ≠ ⊥) :
    ∃ q : ℕ, q.Prime ∧ 𝔭 = Ideal.span {(q : 𝓞 ℚ)} := by
  set e := Rat.ringOfIntegersEquiv
  have hbij : Function.Bijective e := e.bijective
  have hJp : (Ideal.map e 𝔭).IsPrime := Ideal.map_isPrime_of_equiv e
  have hcomap : Ideal.comap e (Ideal.map e 𝔭) = 𝔭 :=
    Ideal.comap_map_of_bijective e hbij
  have hJne : Ideal.map e 𝔭 ≠ ⊥ := by
    intro h
    apply hne
    rw [← hcomap, h, Ideal.comap_bot_of_injective e hbij.injective]
  rcases Ideal.isPrime_int_iff.mp hJp with h | ⟨q, hq, hpJ⟩
  · exact absurd h hJne
  · exact ⟨q, hq, by rw [← hcomap, hpJ, ratSpan_eq_comap_intSpan]⟩

private theorem span_nat_isPrime {q : ℕ} (hq : q.Prime) :
    (Ideal.span {(q : 𝓞 ℚ)}).IsPrime := by
  haveI : (Ideal.span {(q : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hq.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hq)
  rw [ratSpan_eq_comap_intSpan]
  exact Ideal.comap_isPrime Rat.ringOfIntegersEquiv (Ideal.span {(q : ℤ)})

private theorem span_nat_ne_bot {q : ℕ} (hq : q.Prime) :
    Ideal.span {(q : 𝓞 ℚ)} ≠ ⊥ := by
  intro h
  have hnorm : Ideal.absNorm (Ideal.span {(q : 𝓞 ℚ)}) = 0 := by
    rw [Ideal.absNorm_eq_zero_iff]
    exact h
  rw [absNorm_span_nat] at hnorm
  exact hq.ne_zero hnorm

/-- Rational prime ideals of `𝓞 ℚ` are indexed uniquely by rational primes,
with their norm equal to the prime. -/
private noncomputable def rationalPrimeIdealEquiv
    (S : Set (Ideal (𝓞 ℚ))) :
    ↥({q : ℕ | q.Prime ∧ Ideal.span {(q : 𝓞 ℚ)} ∈ S} : Set ℕ) ≃
      {𝔭 : Ideal (𝓞 ℚ) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} := by
  classical
  let f : ↥({q : ℕ | q.Prime ∧ Ideal.span {(q : 𝓞 ℚ)} ∈ S} : Set ℕ) →
      {𝔭 : Ideal (𝓞 ℚ) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} :=
    fun q => ⟨Ideal.span {(q.1 : 𝓞 ℚ)}, q.2.2, span_nat_isPrime q.2.1,
      span_nat_ne_bot q.2.1⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro q r heq
    apply Subtype.ext
    have hnorm := congrArg (fun 𝔭 : {𝔭 : Ideal (𝓞 ℚ) //
      𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} => Ideal.absNorm 𝔭.1) heq
    change Ideal.absNorm (Ideal.span {(q.1 : 𝓞 ℚ)}) =
      Ideal.absNorm (Ideal.span {(r.1 : 𝓞 ℚ)}) at hnorm
    rw [absNorm_span_nat, absNorm_span_nat] at hnorm
    exact hnorm
  · intro 𝔭
    obtain ⟨q, hq, heq⟩ := ratPrime_eq_span 𝔭.1 𝔭.2.2.1 𝔭.2.2.2
    refine ⟨⟨q, hq, ?_⟩, ?_⟩
    · rw [← heq]
      exact 𝔭.2.1
    · apply Subtype.ext
      exact heq.symm

private theorem rationalPrimeIdealEquiv_norm
    (S : Set (Ideal (𝓞 ℚ)))
    (q : ↥({q : ℕ | q.Prime ∧ Ideal.span {(q : 𝓞 ℚ)} ∈ S} : Set ℕ)) :
    Ideal.absNorm ((rationalPrimeIdealEquiv S q).1) = q.1 := by
  change Ideal.absNorm (Ideal.span {(q.1 : 𝓞 ℚ)}) = q.1
  exact absNorm_span_nat q.1

/-- Transfer divergence of reciprocal prime-ideal norms to the corresponding
series over rational primes. -/
private theorem rationalPrimeWeights_not_summable
    (S : Set (Ideal (𝓞 ℚ)))
    (hideal : ¬ Summable
      (fun 𝔭 : {𝔭 : Ideal (𝓞 ℚ) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} =>
        (1 : ℝ) / (Ideal.absNorm 𝔭.1 : ℝ))) :
    ¬ Summable (fun q : ℕ =>
      if q.Prime ∧ Ideal.span {(q : 𝓞 ℚ)} ∈ S then (1 : ℝ) / q else 0) := by
  intro hnat
  let e := rationalPrimeIdealEquiv S
  have hsub : Summable
      (fun q : ↥({q : ℕ | q.Prime ∧ Ideal.span {(q : 𝓞 ℚ)} ∈ S} : Set ℕ) =>
        (1 : ℝ) / q.1) := by
    have hindicator : Summable
        (Set.indicator {q : ℕ | q.Prime ∧ Ideal.span {(q : 𝓞 ℚ)} ∈ S}
          (fun q : ℕ => (1 : ℝ) / q)) := by
      convert hnat using 1
      funext q
      simp [Set.indicator_apply]
    simpa only [Set.mem_ofPred_eq, Function.comp_def] using
      (summable_subtype_iff_indicator.mpr hindicator)
  have hcomp : Summable
      (fun q : ↥({q : ℕ | q.Prime ∧ Ideal.span {(q : 𝓞 ℚ)} ∈ S} : Set ℕ) =>
        (1 : ℝ) / (Ideal.absNorm (e q).1 : ℝ)) := by
    simpa only [e, rationalPrimeIdealEquiv_norm] using hsub
  exact hideal (e.summable_iff.mp hcomp)

/-- At an unramified prime with trivial Frobenius, the residue field above a
rational prime `q` has exactly `q` elements. -/
private theorem residue_card_eq_prime_of_frob_identity
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L] [IsGalois ℚ L]
    (q : ℕ) (hq : q.Prime)
    (hunr : Chebotarev.UnramifiedIn ℚ L (Ideal.span {(q : 𝓞 ℚ)}))
    (hfrob : Chebotarev.frobeniusClass ℚ L (Ideal.span {(q : 𝓞 ℚ)}) =
      ConjClasses.mk 1)
    (P : Ideal (𝓞 L)) [P.IsPrime]
    (hP : P.LiesOver (Ideal.span {(q : 𝓞 ℚ)})) :
    Nat.card (𝓞 L ⧸ P) = q := by
  let p : Ideal (𝓞 ℚ) := Ideal.span {(q : 𝓞 ℚ)}
  letI : p.IsPrime := span_nat_isPrime hq
  letI : P.LiesOver p := hP
  letI : p.IsMaximal := (inferInstance : p.IsPrime).isMaximal (span_nat_ne_bot hq)
  letI : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P p
  have hresidue : Module.finrank (𝓞 ℚ ⧸ P.under (𝓞 ℚ)) (𝓞 L ⧸ P) = 1 := by
    simpa using (Chebotarev.finrank_residue_eq_orderOf ℚ L 1
      (ConjClasses.mk 1) rfl p hunr hfrob P hP)
  have hdegree : P.inertiaDeg (𝓞 ℚ) = 1 := by
    have hunder : P.under (𝓞 ℚ) = p := hP.over.symm
    letI : (P.under (𝓞 ℚ)).IsMaximal := by
      rw [hunder]
      infer_instance
    rw [Ideal.inertiaDeg_eq_of_isMaximal (P.under (𝓞 ℚ)) P]
    exact hresidue
  have hnorm : p.absNorm ^ P.inertiaDeg (𝓞 ℚ) = P.absNorm :=
    Ideal.absNorm_pow_inertiaDeg p P
  have hPnorm : P.absNorm = q := by
    rw [hdegree, pow_one] at hnorm
    rw [← hnorm]
    exact absNorm_span_nat q
  simpa [Ideal.absNorm_apply, Submodule.cardQuot_apply] using hPnorm

/-- The canonical prime field is the residue field at a completely split
prime above `q`. -/
private noncomputable def residue_zmod_equiv_of_frob_identity
    (L : Type*) [Field L] [NumberField L] [Algebra ℚ L] [IsGalois ℚ L]
    (q : ℕ) (hq : q.Prime)
    (hunr : Chebotarev.UnramifiedIn ℚ L (Ideal.span {(q : 𝓞 ℚ)}))
    (hfrob : Chebotarev.frobeniusClass ℚ L (Ideal.span {(q : 𝓞 ℚ)}) =
      ConjClasses.mk 1)
    (P : Ideal (𝓞 L)) [P.IsPrime]
    (hP : P.LiesOver (Ideal.span {(q : 𝓞 ℚ)})) :
    ZMod q ≃+* (𝓞 L ⧸ P) := by
  letI : Finite (𝓞 L ⧸ P) := Chebotarev.UnramifiedIn.finite_quotient ℚ L hunr P hP
  letI : Fintype (𝓞 L ⧸ P) := Fintype.ofFinite _
  exact ZMod.ringEquivOfPrime (𝓞 L ⧸ P) hq (by
    simpa only [Nat.card_eq_fintype_card] using
      residue_card_eq_prime_of_frob_identity L q hq hunr hfrob P hP)

/-- The local conclusion of Lemma 5.1, stated for any Galois number field
containing the roots of the defining polynomial. The prime ideal of `ℚ`
is represented by `span {(q : 𝓞 ℚ)}`. A trivial Frobenius class gives residue
degree one; reduction of the integral roots then supplies the cubic residues
in `ZMod q`. -/
theorem goodPrime_of_split_identity
    (D : Finset ℕ) (L : Type*) [Field L] [NumberField L]
    [Algebra ℚ L] [IsGalois ℚ L]
    (hpoly : ((cubeSplitPolynomial D).map (algebraMap ℚ L)).Splits)
    (q : ℕ) (hq : q.Prime)
    (hclean : ¬ q ∣ 3 * D.prod id)
    (hunr : Chebotarev.UnramifiedIn ℚ L (Ideal.span {(q : 𝓞 ℚ)}))
    (hfrob : Chebotarev.frobeniusClass ℚ L (Ideal.span {(q : 𝓞 ℚ)}) =
      ConjClasses.mk 1) :
    GoodPrime D q := by
  let p : Ideal (𝓞 ℚ) := Ideal.span {(q : 𝓞 ℚ)}
  letI : p.IsPrime := span_nat_isPrime hq
  letI : p.IsMaximal := (inferInstance : p.IsPrime).isMaximal (span_nat_ne_bot hq)
  obtain ⟨P, hPm, hP⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) p
  letI : P.IsPrime := hPm.isPrime
  let e : ZMod q ≃+* (𝓞 L ⧸ P) :=
    residue_zmod_equiv_of_frob_identity L q hq hunr hfrob P hP
  have hcube : ∀ d ∈ D, ∃ x : ZMod q, x ≠ 0 ∧ x ^ 3 = (d : ZMod q) := by
    intro d hd
    obtain ⟨a, ha⟩ := exists_integral_cubic_root_of_splits D L hpoly d hd
    let y : 𝓞 L ⧸ P := Ideal.Quotient.mk P a
    let x : ZMod q := e.symm y
    have ha' : a ^ 3 = (d : 𝓞 L) := by
      apply RingOfIntegers.coe_injective
      simpa using ha
    have hy : y ^ 3 = (d : 𝓞 L ⧸ P) := by
      dsimp [y]
      calc
        (Ideal.Quotient.mk P a) ^ 3 = Ideal.Quotient.mk P (a ^ 3) := by simp
        _ = (d : 𝓞 L ⧸ P) := by simp [ha']
    have hx : x ^ 3 = (d : ZMod q) := by
      apply e.injective
      simpa [x] using hy
    have hqnd : ¬ q ∣ d := by
      intro hqd
      apply hclean
      exact dvd_mul_of_dvd_right (hqd.trans (Finset.dvd_prod_of_mem id hd)) 3
    have hx0 : x ≠ 0 := by
      intro hzero
      have hd0 : (d : ZMod q) = 0 := by simpa [hzero] using hx.symm
      exact hqnd ((ZMod.natCast_eq_zero_iff d q).mp hd0)
    exact ⟨x, hx0, hx⟩
  have hqmod : q % 3 = 1 := by
    obtain ⟨z, hz⟩ := exists_integral_cyclotomic_root_of_splits D L hpoly
    have hz' : z ^ 2 + z + 1 = (0 : 𝓞 L) := by
      apply RingOfIntegers.coe_injective
      simpa using hz
    let y : 𝓞 L ⧸ P := Ideal.Quotient.mk P z
    have hy : y ^ 2 + y + 1 = 0 := by
      simpa [y] using congrArg (Ideal.Quotient.mk P) hz'
    let x : ZMod q := e.symm y
    have hx : x ^ 2 + x + 1 = 0 := by
      apply e.injective
      simpa [x] using hy
    have hq3 : ¬ q ∣ 3 := by
      intro h
      exact hclean (dvd_mul_of_dvd_left h _)
    letI : Fact q.Prime := ⟨hq⟩
    letI : NeZero (3 : ZMod q) := NeZero.of_not_dvd (ZMod q) hq3
    have hroot : (Polynomial.cyclotomic 3 (ZMod q)).IsRoot x := by
      simpa [Polynomial.IsRoot, Polynomial.cyclotomic_three] using hx
    have hprim : IsPrimitiveRoot x 3 :=
      (Polynomial.isRoot_cyclotomic_iff).mp hroot
    have hdiv : 3 ∣ q - 1 := by
      have hx0 : x ≠ 0 := hprim.ne_zero (by decide)
      simpa only [← hprim.eq_orderOf] using ZMod.orderOf_dvd_card_sub_one hx0
    exact ((Nat.modEq_iff_dvd' hq.pos).2 hdiv).symm
  exact ⟨hq, hqmod, hcube⟩

/-- The reciprocal of a suitable prime, and zero at other integers. -/
noncomputable def goodPrimeWeight (D : Finset ℕ) (q : ℕ) : ℝ :=
  if GoodPrime D q then 1 / (q : ℝ) else 0

/-- Positive Dirichlet density forces divergence of the prime-ideal
reciprocal series. This is the analytic step needed after specializing
Chebotarev to the splitting field. -/
private theorem primeIdealReciprocals_not_summable_of_positive_density
    {K : Type*} [Field K] [NumberField K]
    {S : Set (Ideal (𝓞 K))} {δ : ℝ}
    (hS : Chebotarev.HasDirichletDensity S δ) (hδ : 0 < δ) :
    ¬ Summable (fun 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} =>
      (1 : ℝ) / (Ideal.absNorm 𝔭.1 : ℝ)) := by
  intro hsum
  let C : ℝ := ∑' 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭 ∈ S ∧ 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
    (1 : ℝ) / (Ideal.absNorm 𝔭.1 : ℝ)
  have hbound {s : ℝ} (hs : 1 < s) : Chebotarev.primeIdealZetaSum S s ≤ C := by
    rw [Chebotarev.primeIdealZetaSum_def]
    exact Summable.tsum_le_tsum (fun 𝔭 => by
      have hnorm : (1 : ℝ) ≤ (Ideal.absNorm 𝔭.1 : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by
          rw [Ne, Ideal.absNorm_eq_zero_iff]
          exact 𝔭.2.2.2)
      simpa [Real.rpow_neg_one, one_div] using
        (Real.rpow_le_rpow_of_exponent_le hnorm (neg_le_neg hs.le)))
      (hsum.of_nonneg_of_le
        (fun 𝔭 => Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (fun 𝔭 => by
          have hnorm : (1 : ℝ) ≤ (Ideal.absNorm 𝔭.1 : ℝ) := by
            exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by
              rw [Ne, Ideal.absNorm_eq_zero_iff]
              exact 𝔭.2.2.2)
          simpa [Real.rpow_neg_one, one_div] using
            (Real.rpow_le_rpow_of_exponent_le hnorm (neg_le_neg hs.le))))
      hsum
  have hbd : ∀ᶠ s in 𝓝[>] (1 : ℝ), Chebotarev.primeIdealZetaSum S s ≤ C :=
    eventually_nhdsWithin_of_forall (fun _ hs => hbound hs)
  have hzero := Chebotarev.tendsto_primeIdealZetaSum_div_univ_zero_of_le_const K S C hbd
  exact hδ.ne' (tendsto_nhds_unique hS hzero)

/-- Chebotarev supplies primes satisfying all the cubic-residue conditions,
and their reciprocal sum diverges. -/
theorem goodPrimeWeights_diverge (D : Finset ℕ)
    (hD : ∀ d ∈ D, 0 < d) :
    Tendsto (fun N : ℕ =>
      ∑ q ∈ Finset.range N, goodPrimeWeight D q) atTop atTop := by
  classical
  let L := CubeSplitField D
  have hsplit : Chebotarev.HasDirichletDensity
      {𝔭 : Ideal (𝓞 ℚ) | 𝔭.IsPrime ∧ Chebotarev.UnramifiedIn ℚ L 𝔭 ∧
        Chebotarev.frobeniusClass ℚ L 𝔭 = ConjClasses.mk 1}
      ((Module.finrank ℚ L : ℝ)⁻¹) :=
    Chebotarev.density_split_completely
  have hdegree : 0 < Module.finrank ℚ L := Module.finrank_pos
  have hdensity : 0 < ((Module.finrank ℚ L : ℝ)⁻¹) :=
    inv_pos.mpr (Nat.cast_pos.mpr hdegree)
  have hsplitReciprocals :=
    primeIdealReciprocals_not_summable_of_positive_density hsplit hdensity
  let S : Set (Ideal (𝓞 ℚ)) :=
    {𝔭 | 𝔭.IsPrime ∧ Chebotarev.UnramifiedIn ℚ L 𝔭 ∧
      Chebotarev.frobeniusClass ℚ L 𝔭 = ConjClasses.mk 1}
  have hrat : ¬ Summable (fun q : ℕ =>
      if q.Prime ∧ Ideal.span {(q : 𝓞 ℚ)} ∈ S then (1 : ℝ) / q else 0) := by
    intro h
    apply rationalPrimeWeights_not_summable S hsplitReciprocals
    convert h using 1
    funext q
    split_ifs <;> rfl
  let m : ℕ := 3 * D.prod id
  have hmpos : 0 < m := by
    dsimp [m]
    exact mul_pos (by norm_num) (Finset.prod_pos (fun d hd => hD d hd))
  have hbad : Summable (fun q : ℕ => if q ∣ m then (1 : ℝ) / q else 0) := by
    apply summable_of_hasFiniteSupport
    apply (Set.finite_Iic m).subset
    intro q hq
    have hdiv : q ∣ m := by
      by_contra hnot
      simp [hnot] at hq
    exact Nat.le_of_dvd hmpos hdiv
  have hpoly : ((cubeSplitPolynomial D).map (algebraMap ℚ L)).Splits :=
    Polynomial.SplittingField.splits (cubeSplitPolynomial D)
  have hle (q : ℕ) :
      (if q.Prime ∧ Ideal.span {(q : 𝓞 ℚ)} ∈ S then (1 : ℝ) / q else 0) ≤
        goodPrimeWeight D q + (if q ∣ m then (1 : ℝ) / q else 0) := by
    split_ifs with hsplitq hbadq
    · exact le_add_of_nonneg_left (by
        unfold goodPrimeWeight
        split_ifs <;> positivity)
    · have hgood : GoodPrime D q :=
        goodPrime_of_split_identity D L hpoly q hsplitq.1 hbadq
          hsplitq.2.2.1 hsplitq.2.2.2
      simp [goodPrimeWeight, hgood]
    · exact add_nonneg (by
        unfold goodPrimeWeight
        split_ifs <;> positivity) (by positivity)
    · exact add_nonneg (by
        unfold goodPrimeWeight
        split_ifs <;> positivity) (by positivity)
  have hnonneg (q : ℕ) : 0 ≤ goodPrimeWeight D q := by
    unfold goodPrimeWeight
    split_ifs <;> positivity
  have hnonsum : ¬ Summable (goodPrimeWeight D) := by
    intro hgood
    apply hrat
    exact (hgood.add hbad).of_nonneg_of_le (by
      intro q
      split_ifs <;> positivity) hle
  exact (not_summable_iff_tendsto_nat_atTop_of_nonneg hnonneg).mp hnonsum

private theorem goodPrimeWeight_le_one (D : Finset ℕ) (q : ℕ) :
    goodPrimeWeight D q ≤ 1 := by
  unfold goodPrimeWeight
  split_ifs with h
  · have hq0 : (0 : ℝ) < q := by exact_mod_cast h.1.pos
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast h.1.one_le
    exact (div_le_one hq0).2 hq1
  · simp

/-- A finite batch with reciprocal sum in `[T, T + 1]`, as used in equation
(11) of Beyer and de Ryke. -/
theorem finite_goodPrime_batch (D : Finset ℕ)
    (hD : ∀ d ∈ D, 0 < d) (T : ℝ) (hT : 0 ≤ T) :
    ∃ Q : Finset ℕ,
      (∀ q ∈ Q, GoodPrime D q) ∧
      T ≤ ∑ q ∈ Q, (1 : ℝ) / q ∧
      (∑ q ∈ Q, (1 : ℝ) / q) ≤ T + 1 := by
  classical
  rcases eq_or_lt_of_le hT with hzero | hpositive
  · subst T
    refine ⟨∅, ?_, ?_, ?_⟩ <;> simp
  let S (N : ℕ) : ℝ := ∑ q ∈ Finset.range N, goodPrimeWeight D q
  have hexists : ∃ N : ℕ, T ≤ S N :=
    ((goodPrimeWeights_diverge D hD).eventually_ge_atTop T).exists
  have hnonzero : Nat.find hexists ≠ 0 := by
    intro heq
    have hT0 : T ≤ 0 := by
      simpa [heq, S] using (Nat.find_spec hexists)
    exact (not_le_of_gt hpositive) hT0
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hnonzero
  have hprevious : S n < T := by
    have hnlt : n < Nat.find hexists := by
      rw [hn]
      exact Nat.lt_succ_self n
    exact lt_of_not_ge (Nat.find_min hexists hnlt)
  have hcurrent : T ≤ S (n + 1) := by
    simpa [hn] using (Nat.find_spec hexists)
  have hstep : S (n + 1) = S n + goodPrimeWeight D n := by
    simp [S, Finset.sum_range_succ]
  have hcurrentUpper : S (n + 1) ≤ T + 1 := by
    calc
      S (n + 1) = S n + goodPrimeWeight D n := hstep
      _ ≤ T + 1 := add_le_add hprevious.le (goodPrimeWeight_le_one D n)
  let Q := (Finset.range (n + 1)).filter (GoodPrime D)
  have hQ : ∀ q ∈ Q, GoodPrime D q := by
    intro q hq
    exact (Finset.mem_filter.mp hq).2
  have hQsum : (∑ q ∈ Q, (1 : ℝ) / q) = S (n + 1) := by
    simp [Q, S, goodPrimeWeight, Finset.sum_filter]
  exact ⟨Q, hQ, by simpa only [hQsum] using hcurrent,
    by simpa only [hQsum] using hcurrentUpper⟩

end Erdos940
