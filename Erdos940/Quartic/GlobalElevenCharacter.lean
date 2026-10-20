import Erdos940.Quartic.BaseTraceGlobal
import Erdos940.Quartic.GaussianSplitPrimeExistence
import Erdos940.Quartic.JacobiGaussianGenerator
import Erdos940.Quartic.QuarticAnalyticConclusion
import Erdos940.Quartic.QuadraticCharacterLBound

/-!
# Global eleven-character decomposition

Choose a normalized Gaussian prime and its oriented quartic residue
character once for each split rational prime. The resulting eleven real
constituents equal the intrinsic base trace at every good odd prime.
-/

namespace Erdos940.Quartic

/-- Coherent data at one split rational prime, independent of the four
coefficients. -/
structure QuarticSplitPrimeChoice (p : ℕ) [Fact p.Prime] where
  π : GaussianInt
  norm_eq : π.norm = p
  real_odd : (π.re : ZMod 2) = 1
  imag_even : (π.im : ZMod 2) = 0
  ρ : GaussianInt →+* ZMod p
  kernel_eq : ∀ z : GaussianInt, ρ z = 0 ↔ π ∣ z
  χ : MulChar (ZMod p) ℂ
  order_eq : orderOf χ = 4
  character_eq : ∀ x : ZMod p,
    ρ (quarticGaussianLift p χ order_eq x) = x ^ ((p - 1) / 4)
  jacobi_square : jacobiSum χ χ ^ 2 = (π : ℂ) ^ 2

private theorem exists_quarticSplitPrimeChoice
    (p : ℕ) [Fact p.Prime] (hmod : p % 4 = 1) :
    Nonempty (QuarticSplitPrimeChoice p) := by
  obtain ⟨π, hnorm, hre, him⟩ :=
    exists_normalized_gaussian_prime p hmod
  obtain ⟨ρ, hker, χ, hχ, hρchar, hJ⟩ :=
    exists_quartic_residue_character_at_prime p hmod π hnorm hre him
  exact ⟨⟨π, hnorm, hre, him, ρ, hker, χ, hχ, hρchar, hJ⟩⟩

/-- A fixed choice of normalized prime, reduction, and character at a
split rational prime. -/
noncomputable def quarticSplitPrimeChoice
    (p : ℕ) [Fact p.Prime] (hmod : p % 4 = 1) :
    QuarticSplitPrimeChoice p :=
  Classical.choice (exists_quarticSplitPrimeChoice p hmod)

/-- The square of an order-four residue character is the ordinary quadratic
character, viewed in `ℂ`. -/
theorem quarticCharacter_square_eq_quadratic
    (p : ℕ) [Fact p.Prime] (hpodd : p ≠ 2)
    (χ : MulChar (ZMod p) ℂ) (hχ : orderOf χ = 4) :
    χ ^ 2 = (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ) := by
  let ε : MulChar (ZMod p) ℂ :=
    (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)
  have hchar : ringChar (ZMod p) ≠ 2 := by
    simpa [ZMod.ringChar_zmod_n] using hpodd
  obtain ⟨u, hu⟩ := quadraticChar_exists_neg_one' hchar
  have hεne : ε ≠ 1 := by
    intro he
    have hv := congrArg (fun θ : MulChar (ZMod p) ℂ => θ (u : ZMod p)) he
    simp [ε, hu, MulChar.one_apply_coe] at hv
    norm_num at hv
  have hχsqne : χ ^ 2 ≠ 1 := by
    intro he
    have hd := orderOf_dvd_of_pow_eq_one he
    norm_num [hχ] at hd
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hχgne : (χ ^ 2) (g : ZMod p) ≠ 1 := by
    intro he
    exact hχsqne ((MulChar.eq_iff hg (χ ^ 2) 1).2 (by
      simpa [MulChar.one_apply_coe] using he))
  have hεgne : ε (g : ZMod p) ≠ 1 := by
    intro he
    exact hεne ((MulChar.eq_iff hg ε 1).2 (by
      simpa [MulChar.one_apply_coe] using he))
  have hχ4 : χ ^ 4 = 1 := by simpa [hχ] using pow_orderOf_eq_one χ
  have hχg4 : χ (g : ZMod p) ^ 4 = 1 := by
    have hv := congrArg (fun θ : MulChar (ZMod p) ℂ => θ (g : ZMod p)) hχ4
    simpa [MulChar.pow_apply_coe, MulChar.one_apply_coe] using hv
  have hχg2 : (χ ^ 2) (g : ZMod p) = -1 := by
    have hsq : ((χ ^ 2) (g : ZMod p)) ^ 2 = 1 := by
      rw [MulChar.pow_apply_coe]
      simpa [← pow_mul] using hχg4
    exact (sq_eq_one_iff.mp hsq).resolve_left hχgne
  have hεg2 : ε (g : ZMod p) = -1 := by
    have hg0 : (g : ZMod p) ≠ 0 := g.ne_zero
    rcases quadraticChar_isQuadratic (ZMod p) (g : ZMod p) with h0 | h1 | hm
    · exact False.elim (hg0 (quadraticChar_eq_zero_iff.mp h0))
    · exact False.elim (hεgne (by simp [ε, h1]))
    · simp [ε, hm]
  apply (MulChar.eq_iff hg (χ ^ 2) ε).2
  simpa [hχg2, hεg2]

/-- Eleven real constituents at every rational integer. At inert primes
only the quadratic constituent remains; at nonprimes or at two all terms
are set to zero. -/
noncomputable def baseConstituent
    (d : Fin 4 → CanonicalParts) (j : Fin 11) (p : ℕ) : ℝ :=
  if hp : p.Prime then
    letI : Fact p.Prime := ⟨hp⟩
    let a : Fin 4 → ZMod p := fun i => ((d i).val : ZMod p)
    if hsplit : p % 4 = 1 then
      let s := quarticSplitPrimeChoice p hsplit
      (quarticElevenCharacterConstituent p s.χ a s.π j).re
    else if p % 4 = 3 then
      if j = 0 then (quadraticChar (ZMod p) (∏ i, a i) : ℝ) else 0
    else 0
  else 0

theorem baseConstituent_split
    (d : Fin 4 → CanonicalParts) (j : Fin 11) (p : ℕ)
    (hp : p.Prime) (hsplit : p % 4 = 1) :
    baseConstituent d j p =
      letI : Fact p.Prime := ⟨hp⟩
      let s := quarticSplitPrimeChoice p hsplit
      (quarticElevenCharacterConstituent p s.χ
        (fun i => ((d i).val : ZMod p)) s.π j).re := by
  simp only [baseConstituent, dif_pos hp, dif_pos hsplit]

theorem baseConstituent_inert
    (d : Fin 4 → CanonicalParts) (j : Fin 11) (p : ℕ)
    (hp : p.Prime) (hinert : p % 4 = 3) :
    baseConstituent d j p =
      if j = 0 then
        letI : Fact p.Prime := ⟨hp⟩
        (quadraticChar (ZMod p)
          (∏ i, ((d i).val : ZMod p)) : ℝ)
      else 0 := by
  have hsplit : ¬p % 4 = 1 := by omega
  simp only [baseConstituent, dif_pos hp, dif_neg hsplit, if_pos hinert]

/-- The rational constituent is the Legendre symbol of the coefficient
product at every odd prime. -/
theorem baseConstituent_zero_eq_rationalLegendrePrimeValue
    (d : Fin 4 → CanonicalParts) (P : Nat.Primes)
    (hodd : (P : ℕ) ≠ 2) :
    baseConstituent d 0 P =
      rationalLegendrePrimeValue (coefficientProduct d) P := by
  let p : ℕ := P
  have hp : p.Prime := P.property
  letI : Fact p.Prime := ⟨hp⟩
  have hmod : p % 4 = 1 ∨ p % 4 = 3 := by
    have hpodd : Odd p := hp.odd_of_ne_two hodd
    rcases hpodd with ⟨k, hk⟩
    omega
  rcases hmod with hsplit | hinert
  · let s := quarticSplitPrimeChoice p hsplit
    rw [baseConstituent_split d 0 p hp hsplit]
    have hquad := quarticCharacter_square_eq_quadratic
      p hodd s.χ s.order_eq
    have hprod : (coefficientProduct d : ZMod p) =
        ∏ i : Fin 4, ((d i).val : ZMod p) := by
      simp [coefficientProduct]
    simp only [quarticElevenCharacterConstituent]
    rw [hquad]
    simp [rationalLegendrePrimeValue, hodd, legendreSym,
      hprod, coefficientProduct, p]
    norm_cast
  · rw [baseConstituent_inert d 0 p hp hinert]
    have hprod : (coefficientProduct d : ZMod p) =
        ∏ i : Fin 4, ((d i).val : ZMod p) := by
      simp [coefficientProduct]
    simp [rationalLegendrePrimeValue, hodd, legendreSym,
      hprod, coefficientProduct, p]

theorem baseConstituent_zero_eq_rationalLegendrePrimeValue_all
    (d : Fin 4 → CanonicalParts) (P : Nat.Primes) :
    baseConstituent d 0 P =
      rationalLegendrePrimeValue (coefficientProduct d) P := by
  by_cases htwo : (P : ℕ) = 2
  · simp [baseConstituent, rationalLegendrePrimeValue, htwo]
  · exact baseConstituent_zero_eq_rationalLegendrePrimeValue d P htwo

/-- At a good split prime, the globally chosen constituent is exactly the
corresponding Gaussian prime-ideal-symbol constituent. -/
theorem baseConstituent_split_eq_prime_symbol
    (d : Fin 4 → CanonicalParts) (j : Fin 11) (p : ℕ)
    (hp : p.Prime) (hsplit : p % 4 = 1)
    (hunit : ∀ i, ((d i).val : ZMod p) ≠ 0) :
    baseConstituent d j p =
      letI : Fact p.Prime := ⟨hp⟩
      let s := quarticSplitPrimeChoice p hsplit
      let hπ0 : s.π ≠ 0 := gaussianPrime_ne_zero_of_norm p s.π s.norm_eq
      let hρπ : s.ρ s.π = 0 := (s.kernel_eq s.π).2 (dvd_refl s.π)
      (quarticElevenPrimeSymbolConstituent p hsplit s.ρ s.π
        hπ0 hρπ s.χ (fun i => ((d i).val : ZMod p)) hunit j).re := by
  letI : Fact p.Prime := ⟨hp⟩
  let s := quarticSplitPrimeChoice p hsplit
  have hπ0 : s.π ≠ 0 := gaussianPrime_ne_zero_of_norm p s.π s.norm_eq
  have hρπ : s.ρ s.π = 0 := (s.kernel_eq s.π).2 (dvd_refl s.π)
  rw [baseConstituent_split d j p hp hsplit]
  change (quarticElevenCharacterConstituent p s.χ
      (fun i => ((d i).val : ZMod p)) s.π j).re =
    (quarticElevenPrimeSymbolConstituent p hsplit s.ρ s.π hπ0 hρπ
      s.χ (fun i => ((d i).val : ZMod p)) hunit j).re
  rw [quarticElevenCharacterConstituent_eq_prime_symbol
    p hsplit s.ρ s.π hπ0 hρπ s.χ s.order_eq s.character_eq
      (fun i => ((d i).val : ZMod p)) hunit j]

/-- The global eleven real terms sum to the intrinsic base trace at every
good odd prime. -/
theorem quarticBaseTrace_eq_sum_baseConstituent
    (d : Fin 4 → CanonicalParts) (p : ℕ)
    (hp : p.Prime) (hodd : 2 < p)
    (hunit : ∀ i, ((d i).val : ZMod p) ≠ 0) :
    quarticBaseTrace d p = ∑ j : Fin 11, baseConstituent d j p := by
  letI : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have hmod : p % 4 = 1 ∨ p % 4 = 3 := by
    rcases hpodd with ⟨k, hk⟩
    omega
  rcases hmod with hsplit | hinert
  · let s := quarticSplitPrimeChoice p hsplit
    let ψ : AddChar (ZMod p) ℂ :=
      AddChar.FiniteField.primitiveChar_to_Complex (ZMod p)
    have hψ : ψ.IsPrimitive :=
      AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive (ZMod p)
    have htrace := quarticBaseTrace_eq_eleven_real_characters
      d p hp s.χ s.order_eq ψ hψ hunit s.π s.jacobi_square
    simpa only [baseConstituent_split d _ p hp hsplit] using htrace
  · rw [quarticBaseTrace_eq_intrinsic d p hp,
      quarticIntrinsicTrace_eq_quadraticChar_of_inert p hinert _ hunit]
    simp [baseConstituent_inert d _ p hp hinert]

/-- The exact `hBaseCharacter` interface of the analytic conclusion has
no additional finite-sum assumption. -/
theorem baseConstituent_exact_on_base_primes :
    ∀ B, 3 ≤ B → ∀ d : Fin 4 → CanonicalParts,
      ¬ExceptionalTuple d →
      ∀ p ∈ (quarticBasePrimes B).filter
        (fun p => ∀ i, ¬p ∣ (d i).val),
        quarticBaseTrace d p = ∑ j : Fin 11, baseConstituent d j p := by
  intro B _ d _ p hp
  obtain ⟨hbase, hgood⟩ := Finset.mem_filter.mp hp
  obtain ⟨hIcc, hprime⟩ := Finset.mem_filter.mp hbase
  have hodd : 2 < p := by
    have hthree := (Finset.mem_Icc.mp hIcc).1
    omega
  have hunit : ∀ i, ((d i).val : ZMod p) ≠ 0 := by
    intro i hi
    exact hgood i ((ZMod.natCast_eq_zero_iff (d i).val p).mp hi)
  exact quarticBaseTrace_eq_sum_baseConstituent d p hprime hodd hunit

end Erdos940.Quartic
