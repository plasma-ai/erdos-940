import Erdos940.Quartic.PrimeSelector
import Erdos940.Quartic.ProgressionBuilder

/-!
# From Chebotarev prime selection to the inert quartic trace

The character selector applies to finite families of distinct quadratic
characters.  This module translates its output to the coefficient-product
trace of the quartic sieve.
-/

namespace Erdos940.Quartic

open NumberField
open scoped Classical

/-- A summable positive allowance for each positive coefficient product. -/
noncomputable def quarticSelectorWeight (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) / 2 / 2 ^ n

theorem quarticSelectorWeight_pos (n : ℕ) :
    0 < quarticSelectorWeight n := by
  unfold quarticSelectorWeight
  positivity

/-- The prime selector needs nonsquare radicands, rather than squarefree
radicands, once the family is indexed by distinct characters. -/
theorem select_odd_quartic_nonsquare_character_bias
    (E : Finset ℕ) (i : QuarticCharacterField E)
    (hi : i ^ 2 = -1) (hprim : IsPrimitiveRoot i 4)
    {I : Type*} [Fintype I]
    (d : I → ℕ) (a : I → 𝓞 (QuarticCharacterField E))
    (ha : ∀ j, (a j) ^ 2 = (d j : 𝓞 (QuarticCharacterField E)))
    (ha0 : ∀ j, a j ≠ 0)
    (hdpos : ∀ j, 0 < d j)
    (hnsq : ∀ j (b : ℚ), b ^ 2 ≠ (d j : ℚ))
    (hinj : Function.Injective
      (fun j => squareRootGaloisCharacter (QuarticCharacterField E)
        (a j : QuarticCharacterField E) (d j : ℚ)
        (by simpa using congrArg (algebraMap
          (𝓞 (QuarticCharacterField E)) (QuarticCharacterField E)) (ha j))
        (by exact_mod_cast ha0 j)))
    (B : ℕ) (T : ℝ) (hT : 0 ≤ T) (hB4 : 4 ≤ B)
    (hBd : ∀ j, d j ≤ B)
    (hcard : (Fintype.card (OddQuarticAutomorphism E i) : ℝ) ≤ B)
    (hlarge : T + 1 ≤ (B : ℝ))
    (c : I → ℝ) (hc : ∀ j, 0 ≤ c j)
    (hctotal : (∑ j, c j) ≤ (1 / 2 : ℝ)) :
    ∃ Q : Finset ℕ,
      (∀ q ∈ Q, q.Prime ∧ q % 4 = 3 ∧ B < q ∧
        Chebotarev.UnramifiedIn ℚ (QuarticCharacterField E)
          (Ideal.span {(q : 𝓞 ℚ)})) ∧
      (∑ q ∈ Q, (1 : ℝ) / q) ≤ T + 1 ∧
      (∑ q ∈ Q, (1 : ℝ) / (q : ℝ) ^ 2) ≤ 1 ∧
      (∀ j, (∑ q ∈ Q,
        quarticLegendreValue q (d j) * ((1 : ℝ) / q)) ≤
          -T * c j + 1) := by
  classical
  let L := QuarticCharacterField E
  have hax (j : I) : (a j : L) ^ 2 = (d j : L) := by
    simpa using congrArg (algebraMap (𝓞 L) L) (ha j)
  have hax0 (j : I) : (a j : L) ≠ 0 := by
    exact_mod_cast ha0 j
  let χ (j : I) (g : OddQuarticAutomorphism E i) : ℝ :=
    squareRootGaloisCharacter L (a j : L) (d j : ℚ)
      (by simpa using hax j) (hax0 j) g.val
  have hχ (j : I) (g : OddQuarticAutomorphism E i) :
      |χ j g| ≤ 1 := by
    rcases squareRootGaloisCharacter_sign L (a j : L)
        (d j : ℚ) (by simpa using hax j) (hax0 j) g.val with h | h
    · simp [χ, h]
    · simp [χ, h]
  have horth := oddQuartic_squareRootCharacter_orthogonality
    E i hi (fun j => (a j : L)) (fun j => (d j : ℚ))
    (fun j => by simpa using hax j) hax0
    (fun j => by positivity) hnsq hinj
  obtain ⟨Q, hQ, hsum, hsq, hbias⟩ :=
    select_odd_quartic_character_bias E i hi B T hT hcard hlarge
      χ c hc hctotal hχ horth.1 horth.2
  have hcop (q : ℕ) (hq : q.Prime) (hBq : B < q) :
      q.Coprime 4 := by
    apply (Nat.Prime.coprime_iff_not_dvd hq).2
    intro hdiv
    have hqle : q ≤ 4 := Nat.le_of_dvd (by decide) hdiv
    omega
  refine ⟨Q, ?_, hsum, hsq, ?_⟩
  · intro q hq
    obtain ⟨hprime, hBq, hunr, g, hfrob⟩ := hQ q hq
    exact ⟨hprime,
      mod_four_eq_three_of_frobenius_flip L hprim hi g.val
        g.property q hprime (hcop q hprime hBq) hunr hfrob,
      hBq, hunr⟩
  · intro j
    calc
      (∑ q ∈ Q, quarticLegendreValue q (d j) * ((1 : ℝ) / q)) =
          ∑ q ∈ Q, χ j (oddQuarticClassOf E i hi q) *
            ((1 : ℝ) / q) := by
        apply Finset.sum_congr rfl
        intro q hq
        obtain ⟨hprime, hBq, hunr, g, hfrob⟩ := hQ q hq
        letI : Fact q.Prime := ⟨hprime⟩
        have hqd : ¬ q ∣ d j := by
          intro hdiv
          have hqle : q ≤ d j := Nat.le_of_dvd (hdpos j) hdiv
          have hBj := hBd j
          omega
        have hq2 : q ≠ 2 := by omega
        have hleg := squareRootGaloisCharacter_frobenius L q (d j)
          hq2 hqd (a j) (ha j) (ha0 j) g.val hunr hfrob
        rw [oddQuarticClassOf_eq E i hi q g hfrob]
        change quarticLegendreValue q (d j) * ((1 : ℝ) / q) =
          squareRootGaloisCharacter L (a j : L) (d j : ℚ)
            (by simpa using hax j) (hax0 j) g.val * ((1 : ℝ) / q)
        rw [quarticLegendreValue, dif_pos hprime, hleg]
      _ ≤ -T * c j + 1 := hbias j

/-- Select primes with the same negative Legendre-symbol average for every
member of a finite collection of positive nonsquare radicands. Repeated
quadratic characters are removed by indexing the distinct character
functions themselves. -/
theorem select_finite_nonsquare_character_bias
    (E D : Finset ℕ) (hDE : D ⊆ E)
    (hDpos : ∀ d ∈ D, 0 < d)
    (hDnsq : ∀ d ∈ D, ∀ b : ℚ, b ^ 2 ≠ (d : ℚ))
    (i : QuarticCharacterField E) (hi : i ^ 2 = -1)
    (hprim : IsPrimitiveRoot i 4)
    (B : ℕ) (T : ℝ) (hT : 0 ≤ T) (hB4 : 4 ≤ B)
    (hBd : ∀ d ∈ D, d ≤ B)
    (hcard : (Fintype.card (OddQuarticAutomorphism E i) : ℝ) ≤ B)
    (hlarge : T + 1 ≤ (B : ℝ)) :
    ∃ Q : Finset ℕ,
      (∀ q ∈ Q, q.Prime ∧ q % 4 = 3 ∧ B < q) ∧
      (∑ q ∈ Q, (1 : ℝ) / q) ≤ T + 1 ∧
      (∑ q ∈ Q, (1 : ℝ) / (q : ℝ) ^ 2) ≤ 1 ∧
      (∀ d ∈ D, (∑ q ∈ Q,
        quarticLegendreValue q d * ((1 : ℝ) / q)) ≤
          -T * quarticSelectorWeight d + 1) := by
  classical
  let L := QuarticCharacterField E
  let a (x : D) : 𝓞 L :=
    Classical.choose (exists_integral_square_root E x.val (hDE x.property))
  have ha (x : D) : (a x) ^ 2 = (x.val : 𝓞 L) :=
    Classical.choose_spec (exists_integral_square_root E x.val (hDE x.property))
  have ha0 (x : D) : a x ≠ 0 := by
    intro hx
    have hval : (x.val : 𝓞 L) ≠ 0 := by
      exact_mod_cast (hDpos x.val x.property).ne'
    exact hval (by simpa [hx] using (ha x).symm)
  have hax (x : D) : (a x : L) ^ 2 = (x.val : L) := by
    simpa using congrArg (algebraMap (𝓞 L) L) (ha x)
  have hax0 (x : D) : (a x : L) ≠ 0 := by
    exact_mod_cast ha0 x
  let χ (x : D) := squareRootGaloisCharacter L (a x : L)
    (x.val : ℚ) (by simpa using hax x) (hax0 x)
  let chars : Finset (Gal(L/ℚ) →* ℝ) := Finset.univ.image χ
  let I := ↥chars
  let repr (j : I) : D :=
    Classical.choose (Finset.mem_image.mp j.property)
  have hrepr (j : I) : χ (repr j) = j.val :=
    (Classical.choose_spec (Finset.mem_image.mp j.property)).2
  have hinj : Function.Injective (fun j : I => χ (repr j)) := by
    intro j k h
    apply Subtype.ext
    calc
      j.val = χ (repr j) := (hrepr j).symm
      _ = χ (repr k) := h
      _ = k.val := hrepr k
  let c : I → ℝ := fun j =>
    ∑ x : D, if χ x = j.val then quarticSelectorWeight x.val else 0
  have hc (j : I) : 0 ≤ c j := by
    dsimp [c]
    apply Finset.sum_nonneg
    intro x hx
    by_cases h : χ x = j.val
    · simp [h, (quarticSelectorWeight_pos _).le]
    · simp [h]
  have hctotal : (∑ j, c j) ≤ (1 / 2 : ℝ) := by
    have hsum : (∑ j, c j) = ∑ x : D, quarticSelectorWeight x.val := by
      dsimp [c]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      let jx : I := ⟨χ x, Finset.mem_image.mpr
        ⟨x, Finset.mem_univ _, rfl⟩⟩
      have hiff (j : I) : (χ x = j.val) ↔ j = jx := by
        constructor
        · intro h
          apply Subtype.ext
          exact h.symm
        · intro h
          subst j
          rfl
      simp only [hiff]
      simpa using (Finset.sum_ite_eq' (Finset.univ : Finset I) jx
        (fun _ : I => quarticSelectorWeight x.val))
    have hsumD : (∑ x : D, quarticSelectorWeight x.val) =
        ∑ n ∈ D, quarticSelectorWeight n := by
      simpa only [Finset.attach_eq_univ] using
        (Finset.sum_attach D quarticSelectorWeight)
    have hbound : (∑ n ∈ D, quarticSelectorWeight n) ≤ (1 / 2 : ℝ) := by
      have hsumw : Summable quarticSelectorWeight := by
        change Summable (fun n : ℕ => (1 / 2 : ℝ) / 2 / 2 ^ n)
        exact summable_geometric_two' (1 / 2 : ℝ)
      calc
        (∑ n ∈ D, quarticSelectorWeight n) ≤
            ∑' n : ℕ, quarticSelectorWeight n :=
          hsumw.sum_le_tsum D (fun n hn => (quarticSelectorWeight_pos n).le)
        _ = 1 / 2 := by
          simpa only [quarticSelectorWeight] using
            (tsum_geometric_two' (1 / 2 : ℝ))
    calc
      (∑ j, c j) = ∑ x : D, quarticSelectorWeight x.val := hsum
      _ = ∑ n ∈ D, quarticSelectorWeight n := hsumD
      _ ≤ 1 / 2 := hbound
  have horth := oddQuartic_squareRootCharacter_orthogonality
    E i hi (fun j : I => (a (repr j) : L))
    (fun j : I => ((repr j).val : ℚ))
    (fun j => by simpa using hax (repr j))
    (fun j => hax0 (repr j))
    (fun j => by positivity)
    (fun j b => hDnsq (repr j).val (repr j).property b)
    (by simpa only [χ] using hinj)
  let ψ (j : I) (g : OddQuarticAutomorphism E i) : ℝ :=
    χ (repr j) g.val
  have hψ (j : I) (g : OddQuarticAutomorphism E i) : |ψ j g| ≤ 1 := by
    rcases squareRootGaloisCharacter_sign L (a (repr j) : L)
        ((repr j).val : ℚ) (by simpa using hax (repr j))
        (hax0 (repr j)) g.val with h | h
    · simp [ψ, χ, h]
    · simp [ψ, χ, h]
  obtain ⟨Q, hQ, hsum, hsq, hbias⟩ :=
    select_odd_quartic_character_bias E i hi B T hT hcard hlarge
      ψ c hc hctotal hψ (by simpa only [ψ, χ] using horth.1)
      (by simpa only [ψ, χ] using horth.2)
  have hcop (q : ℕ) (hq : q.Prime) (hBq : B < q) : q.Coprime 4 := by
    apply (Nat.Prime.coprime_iff_not_dvd hq).2
    intro hdiv
    have hqle : q ≤ 4 := Nat.le_of_dvd (by decide) hdiv
    omega
  refine ⟨Q, ?_, hsum, hsq, ?_⟩
  · intro q hq
    obtain ⟨hprime, hBq, hunr, g, hfrob⟩ := hQ q hq
    exact ⟨hprime,
      mod_four_eq_three_of_frobenius_flip L hprim hi g.val
        g.property q hprime (hcop q hprime hBq) hunr hfrob,
      hBq⟩
  · intro d hd
    let x : D := ⟨d, hd⟩
    let j : I := ⟨χ x, Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩⟩
    have hchar : χ x = χ (repr j) := (hrepr j).symm
    have heq : (∑ q ∈ Q, quarticLegendreValue q d * ((1 : ℝ) / q)) =
        ∑ q ∈ Q, ψ j (oddQuarticClassOf E i hi q) * ((1 : ℝ) / q) := by
      apply Finset.sum_congr rfl
      intro q hq
      obtain ⟨hprime, hBq, hunr, g, hfrob⟩ := hQ q hq
      letI : Fact q.Prime := ⟨hprime⟩
      have hqd : ¬ q ∣ d := by
        intro hdiv
        have hqle : q ≤ d := Nat.le_of_dvd (hDpos d hd) hdiv
        have hBj := hBd d hd
        omega
      have hqr : ¬ q ∣ (repr j).val := by
        intro hdiv
        have hqle : q ≤ (repr j).val :=
          Nat.le_of_dvd (hDpos _ (repr j).property) hdiv
        have hBj := hBd _ (repr j).property
        omega
      have hq2 : q ≠ 2 := by omega
      have hlegx := squareRootGaloisCharacter_frobenius L q d
        hq2 hqd (a x) (ha x) (ha0 x) g.val hunr hfrob
      have hlegr := squareRootGaloisCharacter_frobenius L q (repr j).val
        hq2 hqr (a (repr j)) (ha (repr j)) (ha0 (repr j))
        g.val hunr hfrob
      have hvalues : quarticLegendreValue q d =
          ψ j (oddQuarticClassOf E i hi q) := by
        rw [oddQuarticClassOf_eq E i hi q g hfrob]
        change quarticLegendreValue q d = χ (repr j) g.val
        rw [quarticLegendreValue, dif_pos hprime]
        calc
          (legendreSym q d : ℝ) = χ x g.val := hlegx.symm
          _ = χ (repr j) g.val :=
            congrArg (fun f : Gal(L/ℚ) →* ℝ => f g.val) hchar
      rw [hvalues]
    rw [heq]
    have hcle : quarticSelectorWeight d ≤ c j := by
      have hsingle :
          (if χ x = j.val then quarticSelectorWeight x.val else 0) ≤
            ∑ y : D, if χ y = j.val then quarticSelectorWeight y.val else 0 := by
        exact Finset.single_le_sum
          (s := (Finset.univ : Finset D))
          (f := fun y : D => if χ y = j.val then quarticSelectorWeight y.val else 0)
          (fun y hy => by
            by_cases h : χ y = j.val
            · simp [h, (quarticSelectorWeight_pos _).le]
            · simp [h])
          (Finset.mem_univ x)
      have hterm : (if χ x = j.val then quarticSelectorWeight x.val else 0) =
          quarticSelectorWeight d := by
        simp [j, x]
      simpa only [c, hterm] using hsingle
    calc
      (∑ q ∈ Q, ψ j (oddQuarticClassOf E i hi q) * ((1 : ℝ) / q)) ≤
          -T * c j + 1 := hbias j
      _ ≤ -T * quarticSelectorWeight d + 1 := by
        have hmul := mul_le_mul_of_nonneg_left hcle hT
        linarith

/-- All coefficient products formed from four coefficients in `E`. -/
noncomputable def quarticFiniteCoefficientProducts
    (E : Finset CanonicalParts) : Finset ℕ :=
  (Fintype.piFinset (fun _ : Fin 4 => E)).image coefficientProduct

/-- The regular coefficient products. Positive square products belong to
the exceptional family and are not selected for a negative trace. -/
noncomputable def quarticRegularCoefficientProducts
    (E : Finset CanonicalParts) : Finset ℕ :=
  (quarticFiniteCoefficientProducts E).filter
    (fun n => ∀ b : ℚ, b ^ 2 ≠ (n : ℚ))

theorem quarticFiniteCoefficientProducts_mem
    (E : Finset CanonicalParts) (d : Fin 4 → CanonicalParts)
    (hd : ∀ j, d j ∈ E) :
    coefficientProduct d ∈ quarticFiniteCoefficientProducts E := by
  classical
  apply Finset.mem_image.mpr
  exact ⟨d, Fintype.mem_piFinset.mpr hd, rfl⟩

theorem coefficientProduct_pos_for_selector
    (d : Fin 4 → CanonicalParts) : 0 < coefficientProduct d := by
  unfold coefficientProduct
  exact Finset.prod_pos fun j _ => (d j).property.pos

theorem regular_coefficientProduct_nonsquare
    (d : Fin 4 → CanonicalParts) (hreg : ¬ ExceptionalTuple d)
    (b : ℚ) : b ^ 2 ≠ (coefficientProduct d : ℚ) := by
  intro hsq
  apply hreg
  left
  refine ⟨b, ?_⟩
  simpa only [coefficientProduct, Nat.cast_prod] using hsq

theorem quarticRegularCoefficientProducts_mem
    (E : Finset CanonicalParts) (d : Fin 4 → CanonicalParts)
    (hd : ∀ j, d j ∈ E) (hreg : ¬ ExceptionalTuple d) :
    coefficientProduct d ∈ quarticRegularCoefficientProducts E := by
  classical
  apply Finset.mem_filter.mpr
  exact ⟨quarticFiniteCoefficientProducts_mem E d hd,
    regular_coefficientProduct_nonsquare d hreg⟩

/-- Every finite coefficient set has a simultaneous supply of inert primes
biased against the coefficient products of all its regular tuples. The
positive bias rate is uniform within this finite set. -/
theorem select_finite_quartic_coefficient_bias
    (E : Finset CanonicalParts)
    (i : QuarticCharacterField (quarticRegularCoefficientProducts E))
    (hi : i ^ 2 = -1) (hprim : IsPrimitiveRoot i 4)
    (C : ℕ) (T : ℝ) (hT : 0 ≤ T) (hC4 : 4 ≤ C)
    (hCprod : ∀ n ∈ quarticRegularCoefficientProducts E, n ≤ C)
    (hcard : (Fintype.card
      (OddQuarticAutomorphism (quarticRegularCoefficientProducts E) i) : ℝ) ≤ C)
    (hlarge : T + 1 ≤ (C : ℝ)) :
    ∃ Q : Finset ℕ,
      (∀ q ∈ Q, q.Prime ∧ q % 4 = 3 ∧ C < q) ∧
      (∑ q ∈ Q, (1 : ℝ) / q) ≤ T + 1 ∧
      (∑ q ∈ Q, (1 : ℝ) / (q : ℝ) ^ 2) ≤ 1 ∧
      (∀ d : Fin 4 → CanonicalParts, ¬ ExceptionalTuple d →
        (∀ j, d j ∈ E) →
        (∑ q ∈ Q, quarticLegendreValue q (coefficientProduct d) *
          ((1 : ℝ) / q)) ≤
            -T * quarticSelectorWeight (coefficientProduct d) + 1) := by
  have hpos : ∀ n ∈ quarticRegularCoefficientProducts E, 0 < n := by
    intro n hn
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp
      (Finset.mem_filter.mp hn).1
    exact coefficientProduct_pos_for_selector d
  obtain ⟨Q, hQ, hsum, hsq, hbias⟩ :=
    select_finite_nonsquare_character_bias
      (quarticRegularCoefficientProducts E)
      (quarticRegularCoefficientProducts E) (Finset.Subset.refl _)
      hpos (fun n hn => (Finset.mem_filter.mp hn).2)
      i hi hprim C T hT hC4 hCprod hcard hlarge
  refine ⟨Q, hQ, hsum, hsq, ?_⟩
  intro d hreg hd
  exact hbias (coefficientProduct d)
    (quarticRegularCoefficientProducts_mem E d hd hreg)

private theorem primitive_fourth_root_sq_eq_neg_one
    {K : Type*} [Field K] (i : K) (hprim : IsPrimitiveRoot i 4) :
    i ^ 2 = -1 := by
  have hfour : i ^ 4 = 1 := hprim.pow_eq_one
  have htwo : i ^ 2 ≠ 1 := by
    intro h
    have hdiv : 4 ∣ 2 := (hprim.pow_eq_one_iff_dvd 2).mp h
    norm_num at hdiv
  have hsq : (i ^ 2) ^ 2 = (1 : K) ^ 2 := by
    calc
      (i ^ 2) ^ 2 = i ^ 4 := by ring
      _ = 1 := hfour
      _ = 1 ^ 2 := by ring
  rcases eq_or_eq_neg_of_sq_eq_sq (i ^ 2) 1 hsq with h | h
  · exact (htwo h).elim
  · simpa using h

/-- The cutoff can always be enlarged to contain every coefficient
product, the finite Galois group, and the requested prime budget. -/
theorem exists_selected_quartic_coefficient_bias
    (E : Finset CanonicalParts) (B T : ℕ) :
    ∃ Q : Finset ℕ,
      (∀ q ∈ Q, q.Prime ∧ q % 4 = 3 ∧ B < q) ∧
      (∑ q ∈ Q, (1 : ℝ) / q) ≤ (T : ℝ) + 1 ∧
      (∑ q ∈ Q, (1 : ℝ) / (q : ℝ) ^ 2) ≤ 1 ∧
      (∀ d : Fin 4 → CanonicalParts, ¬ ExceptionalTuple d →
        (∀ j, d j ∈ E) → ∀ q ∈ Q, coefficientProduct d < q) ∧
      (∀ d : Fin 4 → CanonicalParts, ¬ ExceptionalTuple d →
        (∀ j, d j ∈ E) →
        (∑ q ∈ Q, quarticLegendreValue q (coefficientProduct d) *
          ((1 : ℝ) / q)) ≤
            -(T : ℝ) * quarticSelectorWeight (coefficientProduct d) + 1) := by
  classical
  let F := quarticRegularCoefficientProducts E
  obtain ⟨i, hprim⟩ := exists_primitive_fourth_root F
  have hi : i ^ 2 = -1 := primitive_fourth_root_sq_eq_neg_one i hprim
  let C : ℕ := max B (max 4
    (max (F.sup id) (max (T + 1)
      (Fintype.card (OddQuarticAutomorphism F i)))))
  have hC4 : 4 ≤ C := by dsimp [C]; omega
  have hCB : B ≤ C := by dsimp [C]; omega
  have hCprod : ∀ n ∈ F, n ≤ C := by
    intro n hn
    have hn' : n ≤ F.sup id := by
      simpa only [id_eq] using (Finset.le_sup (f := id) hn)
    dsimp [C]
    omega
  have hCcard : Fintype.card (OddQuarticAutomorphism F i) ≤ C := by
    dsimp [C]
    omega
  have hCcardR :
      (Fintype.card (OddQuarticAutomorphism F i) : ℝ) ≤ C := by
    exact_mod_cast hCcard
  have hClarge : (T : ℝ) + 1 ≤ (C : ℝ) := by
    have hnat : T + 1 ≤ C := by dsimp [C]; omega
    exact_mod_cast hnat
  obtain ⟨Q, hQ, hsum, hsq, hbias⟩ :=
    select_finite_quartic_coefficient_bias E i hi hprim C (T : ℝ)
      (by positivity) hC4 hCprod hCcardR hClarge
  refine ⟨Q, ?_, hsum, hsq, ?_, hbias⟩
  · intro q hq
    obtain ⟨hp, hmod, hCq⟩ := hQ q hq
    exact ⟨hp, hmod, lt_of_le_of_lt hCB hCq⟩
  · intro d hreg hd q hq
    have hmem := quarticRegularCoefficientProducts_mem E d hd hreg
    exact lt_of_le_of_lt (hCprod _ hmem) (hQ q hq).2.2

/-- The selected trace is the Legendre symbol of the four coefficient
product, interpreted as a real number at a prime modulus. -/
noncomputable def quarticSelectedTrace
    (d : Fin 4 → CanonicalParts) (q : ℕ) : ℝ :=
  quarticLegendreValue q (coefficientProduct d)

/-- All selected-prime inputs for the finite arithmetic progression. -/
structure QuarticSelectedPrimePackage
    (T B : ℕ) (E : Finset CanonicalParts) where
  Q : Finset ℕ
  prime : ∀ q ∈ Q, q.Prime ∧ 2 < q
  inert : ∀ q ∈ Q, q % 4 = 3
  far : ∀ q ∈ Q, B < q
  budget : (∑ q ∈ Q, (q : ℝ)⁻¹) ≤ (T : ℝ) + 1
  squares : (∑ q ∈ Q, (1 : ℝ) / (q : ℝ) ^ 2) ≤ 1
  unit : ∀ d, ¬ ExceptionalTuple d → (∀ j, d j ∈ E) →
    ∀ q ∈ Q, ∀ j, ((d j).val : ZMod q) ≠ 0
  four : ∀ q ∈ Q, (4 : ZMod q) ≠ 0
  trace : ∀ d, ¬ ExceptionalTuple d → (∀ j, d j ∈ E) →
    ∀ q ∈ Q,
      (Nat.card {y : Fin 4 → ZMod q //
        (∑ j, ((d j).val : ZMod q) * y j ^ 4) = 0} : ℝ) /
          (q : ℝ) ^ 3 =
        1 + quarticSelectedTrace d q *
          ((q : ℝ)⁻¹ - ((q : ℝ) ^ 2)⁻¹)
  traceLower : ∀ d, ¬ ExceptionalTuple d → (∀ j, d j ∈ E) →
    ∀ q ∈ Q, -(quarticSelectedTrace d q) ≤ 1
  bias : ∀ d, ¬ ExceptionalTuple d → (∀ j, d j ∈ E) →
    (∑ q ∈ Q, quarticSelectedTrace d q / (q : ℝ)) ≤
      -(T : ℝ) * quarticSelectorWeight (coefficientProduct d) + 1

/-- Chebotarev selection and the inert-prime local calculation supply the
complete selected-prime package for any finite coefficient set. -/
theorem exists_quartic_selected_prime_package
    (T B : ℕ) (E : Finset CanonicalParts) :
    Nonempty (QuarticSelectedPrimePackage T B E) := by
  classical
  obtain ⟨Q, hQ, hsum, hsq, hfarprod, hbias⟩ :=
    exists_selected_quartic_coefficient_bias E B T
  have hunit : ∀ d : Fin 4 → CanonicalParts,
      ¬ ExceptionalTuple d → (∀ j, d j ∈ E) →
      ∀ q ∈ Q, ∀ j, ((d j).val : ZMod q) ≠ 0 := by
    intro d hreg hd q hq j hzero
    have hqdiv : q ∣ (d j).val := (ZMod.natCast_eq_zero_iff _ _).mp hzero
    have hqle : q ≤ (d j).val := Nat.le_of_dvd (d j).property.pos hqdiv
    have hjdvd : (d j).val ∣ coefficientProduct d := by
      unfold coefficientProduct
      exact Finset.dvd_prod_of_mem (fun k => (d k).val) (Finset.mem_univ j)
    have hjle : (d j).val ≤ coefficientProduct d :=
      Nat.le_of_dvd (coefficientProduct_pos_for_selector d) hjdvd
    have hprodq := hfarprod d hreg hd q hq
    omega
  refine ⟨{
    Q := Q
    prime := ?_
    inert := ?_
    far := ?_
    budget := ?_
    squares := hsq
    unit := hunit
    four := ?_
    trace := ?_
    traceLower := ?_
    bias := ?_
  }⟩
  · intro q hq
    obtain ⟨hp, hmod, hBq⟩ := hQ q hq
    have hmodle : q % 4 ≤ q := Nat.mod_le _ _
    exact ⟨hp, by omega⟩
  · intro q hq
    exact (hQ q hq).2.1
  · intro q hq
    exact (hQ q hq).2.2
  · simpa only [one_div] using hsum
  · intro q hq hzero
    have hqdiv : q ∣ 4 := (ZMod.natCast_eq_zero_iff _ _).mp hzero
    have hqle : q ≤ 4 := Nat.le_of_dvd (by decide) hqdiv
    have hqmod := (hQ q hq).2.1
    interval_cases q <;> norm_num at *
  · intro d hreg hd q hq
    letI : Fact q.Prime := ⟨(hQ q hq).1⟩
    have htrace := quarticInertRealTrace q (hQ q hq).2.1 d
      (hunit d hreg hd q hq)
    simpa only [quarticSelectedTrace, quarticLegendreValue,
      dif_pos (hQ q hq).1] using htrace
  · intro d hreg hd q hq
    letI : Fact q.Prime := ⟨(hQ q hq).1⟩
    have hD : ((coefficientProduct d : ℤ) : ZMod q) ≠ 0 := by
      have hprod : (∏ j, ((d j).val : ZMod q)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr (fun j _ => hunit d hreg hd q hq j)
      simpa [coefficientProduct, Nat.cast_prod] using hprod
    rcases legendreSym.eq_one_or_neg_one q hD with h | h <;>
      simp [quarticSelectedTrace, quarticLegendreValue,
        (hQ q hq).1, h]
  · intro d hreg hd
    simpa [quarticSelectedTrace, div_eq_mul_inv, one_div] using
      hbias d hreg hd

end Erdos940.Quartic
