import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Four-variable quadratic zero count

For odd finite fields, a nondegenerate diagonal quadratic form in four
variables has `q³ + (q - 1) q χ(∏ aᵢ)` zeroes.  The proof below uses the
elementary binary-form count, rather than an additive Gauss sum.
-/

namespace Erdos940.Quartic

open Finset

section FiniteField

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] [DecidableEq F] in
private theorem sq_sub_sq_eq_mul (x y : F) : x ^ 2 - y ^ 2 = (x + y) * (x - y) := by
  ring

private noncomputable def sumDiffEquiv (h2 : (2 : F) ≠ 0) : F × F ≃ F × F where
  toFun p := (p.1 + p.2, p.1 - p.2)
  invFun p := ((p.1 + p.2) / 2, (p.1 - p.2) / 2)
  left_inv p := by
    apply Prod.ext <;> dsimp
    · field_simp
      ring
    · field_simp
      ring
  right_inv p := by
    apply Prod.ext <;> dsimp
    · field_simp
      ring
    · field_simp
      ring

private noncomputable def squareDifferenceEquiv (h2 : (2 : F) ≠ 0) (t : F) :
    {p : F × F // p.1 ^ 2 - p.2 ^ 2 = t} ≃
      {p : F × F // p.1 * p.2 = t} :=
  (sumDiffEquiv h2).subtypeEquiv fun p => by
    simp only [sumDiffEquiv, Equiv.coe_fn_mk, sq_sub_sq_eq_mul]

private noncomputable def hyperbolaEquiv (t : F) (ht : t ≠ 0) :
    {p : F × F // p.1 * p.2 = t} ≃ {u : F // u ≠ 0} where
  toFun p := ⟨p.1.1, fun hu => ht (by simpa [hu] using p.2.symm)⟩
  invFun u := ⟨(u.1, t / u.1), by field_simp [u.2]⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have hu : p.1.1 ≠ 0 := fun h => ht (by simpa [h] using p.2.symm)
      dsimp
      symm
      apply (eq_div_iff hu).2
      simpa [mul_comm] using p.2
  right_inv u := by rfl

private theorem card_nonzero : Fintype.card {u : F // u ≠ 0} = Fintype.card F - 1 := by
  classical
  rw [Fintype.card_subtype_compl (fun u : F => u = 0)]
  simp

private theorem card_square_difference (h2 : (2 : F) ≠ 0) (t : F) (ht : t ≠ 0) :
    Fintype.card {p : F × F // p.1 ^ 2 - p.2 ^ 2 = t} = Fintype.card F - 1 := by
  rw [Fintype.card_congr (squareDifferenceEquiv h2 t),
    Fintype.card_congr (hyperbolaEquiv t ht), card_nonzero]

private def squareDifferenceSigma (t : F) :
    {p : F × F // p.1 ^ 2 - p.2 ^ 2 = t} ≃
      Σ x : F, {y : F // y ^ 2 = x ^ 2 - t} where
  toFun p := ⟨p.1.1, ⟨p.1.2, by
    have h := p.2
    linear_combination -h⟩⟩
  invFun p := ⟨(p.1, p.2.1), by
    have h := p.2.2
    linear_combination -h⟩
  left_inv p := by rfl
  right_inv p := by rfl

private theorem card_sqrt_eq_char_add_one (h2 : (2 : F) ≠ 0) (a : F) :
    (Fintype.card {y : F // y ^ 2 = a} : ℤ) = quadraticChar F a + 1 := by
  classical
  have hchar : ringChar F ≠ 2 := by
    intro h
    exact h2 ((ringChar.spec F 2).2 (by rw [h]))
  simpa [Fintype.card_subtype, Set.toFinset_ofPred] using
    (quadraticChar_card_sqrts hchar a)

/-- The elementary character correlation at a nonzero displacement. -/
theorem quadraticChar_sum_sq_sub (h2 : (2 : F) ≠ 0) (t : F) (ht : t ≠ 0) :
    (∑ x : F, quadraticChar F (x ^ 2 - t)) = -1 := by
  classical
  have hc : (∑ x : F, Fintype.card {y : F // y ^ 2 = x ^ 2 - t}) + 1 =
      Fintype.card F := by
    rw [← Fintype.card_sigma, ← Fintype.card_congr (squareDifferenceSigma t),
      card_square_difference h2 t ht]
    exact Nat.sub_add_cancel (Fintype.card_pos : 1 ≤ Fintype.card F)
  have hc' : (∑ x : F, (Fintype.card {y : F // y ^ 2 = x ^ 2 - t} : ℤ)) + 1 =
      (Fintype.card F : ℤ) := by
    exact_mod_cast hc
  simp_rw [card_sqrt_eq_char_add_one h2] at hc'
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one] at hc'
  omega

private def binaryFormSigma (a b t : F) (hb : b ≠ 0) :
    {p : F × F // a * p.1 ^ 2 + b * p.2 ^ 2 = t} ≃
      Σ x : F, {y : F // y ^ 2 = (t - a * x ^ 2) / b} where
  toFun p := ⟨p.1.1, ⟨p.1.2, by
    apply (eq_div_iff hb).2
    linear_combination p.2⟩⟩
  invFun p := ⟨(p.1, p.2.1), by
    have h := (eq_div_iff hb).1 p.2.2
    linear_combination h⟩
  left_inv p := by rfl
  right_inv p := by rfl

private theorem binaryForm_card_nonzero (h2 : (2 : F) ≠ 0)
    (a b t : F) (ha : a ≠ 0) (hb : b ≠ 0) (ht : t ≠ 0) :
    (Fintype.card {p : F × F // a * p.1 ^ 2 + b * p.2 ^ 2 = t} : ℤ) =
      (Fintype.card F : ℤ) - quadraticChar F (-a * b) := by
  classical
  have hfrac : t / a ≠ 0 := div_ne_zero ht ha
  have hfactor (x : F) :
      (t - a * x ^ 2) / b = (-a / b) * (x ^ 2 - t / a) := by
    field_simp
    ring
  have hχ : quadraticChar F (-a / b) = quadraticChar F (-a * b) := by
    have hprod : (-a / b) * b ^ 2 = -a * b := by
      field_simp
    calc
      quadraticChar F (-a / b) = quadraticChar F ((-a / b) * b ^ 2) := by
        rw [map_mul, quadraticChar_sq_one' hb, mul_one]
      _ = quadraticChar F (-a * b) := by rw [hprod]
  have hcard :
      (Fintype.card {p : F × F // a * p.1 ^ 2 + b * p.2 ^ 2 = t} : ℤ) =
        ∑ x : F, (quadraticChar F ((t - a * x ^ 2) / b) + 1) := by
    rw [Fintype.card_congr (binaryFormSigma a b t hb), Fintype.card_sigma]
    push_cast
    exact Finset.sum_congr rfl (fun x _ => card_sqrt_eq_char_add_one h2 _)
  rw [hcard]
  simp only [map_mul] at hχ
  simp_rw [hfactor, map_mul]
  simp only [Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [← Finset.mul_sum, quadraticChar_sum_sq_sub h2 (t / a) hfrac, hχ]
  ring

private def binaryFormTargetEquiv (a b : F) :
    F × F ≃ Σ t : F, {p : F × F // a * p.1 ^ 2 + b * p.2 ^ 2 = t} where
  toFun p := ⟨a * p.1 ^ 2 + b * p.2 ^ 2, p, rfl⟩
  invFun p := p.2.1
  left_inv p := rfl
  right_inv p := by rcases p with ⟨t, ⟨p, hp⟩⟩; cases hp; rfl

private theorem binaryForm_card_zero (h2 : (2 : F) ≠ 0)
    (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    (Fintype.card {p : F × F // a * p.1 ^ 2 + b * p.2 ^ 2 = 0} : ℤ) =
      (Fintype.card F : ℤ) + ((Fintype.card F : ℤ) - 1) *
        quadraticChar F (-a * b) := by
  classical
  let N (t : F) : ℤ :=
    (Fintype.card {p : F × F // a * p.1 ^ 2 + b * p.2 ^ 2 = t} : ℤ)
  have htotal : (∑ t : F, N t) = (Fintype.card F : ℤ) ^ 2 := by
    dsimp [N]
    rw [← Nat.cast_sum, ← Fintype.card_sigma,
      ← Fintype.card_congr (binaryFormTargetEquiv a b)]
    simp [Fintype.card_prod, pow_two]
  have hother (t : F) (ht : t ≠ 0) :
      N t = (Fintype.card F : ℤ) - quadraticChar F (-a * b) :=
    binaryForm_card_nonzero h2 a b t ha hb ht
  have hsum :
      (∑ t ∈ (Finset.univ : Finset F).erase 0, N t) =
        ((Fintype.card F : ℤ) - 1) *
          ((Fintype.card F : ℤ) - quadraticChar F (-a * b)) := by
    rw [Finset.sum_congr rfl (fun t ht => hother t (Finset.ne_of_mem_erase ht)),
      Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ 0)]
    simp only [Finset.card_univ, nsmul_eq_mul]
    have hpos : 1 ≤ Fintype.card F := Fintype.card_pos
    rw [Nat.cast_sub hpos]
    norm_num
  have hsplit : N 0 + ∑ t ∈ (Finset.univ : Finset F).erase 0, N t =
      (Fintype.card F : ℤ) ^ 2 := by
    rw [Finset.add_sum_erase _ N (Finset.mem_univ 0)]
    exact htotal
  dsimp [N] at hsplit ⊢
  rw [hsum] at hsplit
  nlinarith

private def finFourPairsEquiv : (Fin 4 → F) ≃ (F × F) × (F × F) where
  toFun x := ((x 0, x 1), (x 2, x 3))
  invFun p := ![p.1.1, p.1.2, p.2.1, p.2.2]
  left_inv x := by
    funext i
    fin_cases i <;> rfl
  right_inv p := by
    rcases p with ⟨⟨x, y⟩, ⟨z, w⟩⟩
    rfl

private def binaryForm (a b : F) (p : F × F) : F := a * p.1 ^ 2 + b * p.2 ^ 2

private def fourFormPairsEquiv (a : Fin 4 → F) :
    {x : Fin 4 → F // ∑ i, a i * x i ^ 2 = 0} ≃
      {p : (F × F) × (F × F) //
        binaryForm (a 0) (a 1) p.1 + binaryForm (a 2) (a 3) p.2 = 0} :=
  finFourPairsEquiv.subtypeEquiv (fun x => by
    simp only [Fin.sum_univ_four, binaryForm, finFourPairsEquiv, Equiv.coe_fn_mk]
    simp only [add_assoc])

private def fourFormFiberEquiv (a b c d : F) :
    {p : (F × F) × (F × F) // binaryForm a b p.1 + binaryForm c d p.2 = 0} ≃
      Σ t : F,
        {v : F × F // binaryForm a b v = t} ×
          {w : F × F // binaryForm c d w = -t} where
  toFun p := ⟨binaryForm a b p.1.1,
    ⟨⟨p.1.1, rfl⟩, ⟨p.1.2, by
      dsimp [binaryForm] at p ⊢
      linear_combination p.2⟩⟩⟩
  invFun p := ⟨(p.2.1.1, p.2.2.1), by
    have h := p.2.1.2
    have h' := p.2.2.2
    dsimp [binaryForm] at h h' ⊢
    linear_combination h + h'⟩
  left_inv p := by rfl
  right_inv p := by
    rcases p with ⟨t, ⟨⟨v, hv⟩, ⟨w, hw⟩⟩⟩
    cases hv
    rfl

/-- The zero count of a nondegenerate four-variable diagonal quadratic form over
an odd finite field. -/
theorem quadratic_four_zero_count (h2 : (2 : F) ≠ 0)
    (a : Fin 4 → F) (ha : ∀ i, a i ≠ 0) :
    (Fintype.card {x : Fin 4 → F // ∑ i, a i * x i ^ 2 = 0} : ℤ) =
      (Fintype.card F : ℤ) ^ 3 +
        ((Fintype.card F : ℤ) - 1) * (Fintype.card F : ℤ) *
          quadraticChar F (∏ i, a i) := by
  classical
  let A (t : F) : ℤ :=
    (Fintype.card {p : F × F // binaryForm (a 0) (a 1) p = t} : ℤ)
  let B (t : F) : ℤ :=
    (Fintype.card {p : F × F // binaryForm (a 2) (a 3) p = t} : ℤ)
  let q : ℤ := Fintype.card F
  let c : ℤ := quadraticChar F (-(a 0) * a 1)
  let d : ℤ := quadraticChar F (-(a 2) * a 3)
  have hA0 : A 0 = q + (q - 1) * c :=
    binaryForm_card_zero h2 (a 0) (a 1) (ha 0) (ha 1)
  have hB0 : B 0 = q + (q - 1) * d :=
    binaryForm_card_zero h2 (a 2) (a 3) (ha 2) (ha 3)
  have hA (t : F) (ht : t ≠ 0) : A t = q - c :=
    binaryForm_card_nonzero h2 (a 0) (a 1) t (ha 0) (ha 1) ht
  have hB (t : F) (ht : t ≠ 0) : B (-t) = q - d :=
    binaryForm_card_nonzero h2 (a 2) (a 3) (-t) (ha 2) (ha 3)
      (neg_ne_zero.mpr ht)
  have hcount :
      (Fintype.card {x : Fin 4 → F // ∑ i, a i * x i ^ 2 = 0} : ℤ) =
        ∑ t : F, A t * B (-t) := by
    rw [Fintype.card_congr (fourFormPairsEquiv a),
      Fintype.card_congr (fourFormFiberEquiv (a 0) (a 1) (a 2) (a 3)),
      Fintype.card_sigma]
    push_cast
    exact Finset.sum_congr rfl (fun t _ => by
      simp only [Fintype.card_prod, Nat.cast_mul]
      rfl)
  have hsum :
      (∑ t ∈ (Finset.univ : Finset F).erase 0, A t * B (-t)) =
        (q - 1) * ((q - c) * (q - d)) := by
    rw [Finset.sum_congr rfl (fun t ht => by
      rw [hA t (Finset.ne_of_mem_erase ht), hB t (Finset.ne_of_mem_erase ht)]),
      Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ 0)]
    simp only [Finset.card_univ, nsmul_eq_mul]
    dsimp [q]
    rw [Nat.cast_sub (Fintype.card_pos : 1 ≤ Fintype.card F)]
    norm_num
  have hprod : c * d = quadraticChar F (∏ i, a i) := by
    dsimp [c, d]
    rw [← map_mul]
    congr 1
    rw [Fin.prod_univ_four]
    ring
  rw [hcount, ← Finset.add_sum_erase (Finset.univ : Finset F)
    (fun t => A t * B (-t)) (Finset.mem_univ 0)]
  rw [hA0]
  simp only [neg_zero]
  rw [hB0, hsum]
  dsimp [q]
  rw [← hprod]
  ring

end FiniteField

section ZMod

variable {q : ℕ} [Fact q.Prime]

/-- The four-variable quadratic zero count modulo an odd prime. -/
theorem zmod_quadratic_four_zero_count (hodd : q ≠ 2)
    (a : Fin 4 → ZMod q) (ha : ∀ i, a i ≠ 0) :
    (Fintype.card {x : Fin 4 → ZMod q // ∑ i, a i * x i ^ 2 = 0} : ℤ) =
      (q : ℤ) ^ 3 + ((q : ℤ) - 1) * (q : ℤ) *
        quadraticChar (ZMod q) (∏ i, a i) := by
  have hchar : ringChar (ZMod q) ≠ 2 := by
    simpa only [ZMod.ringChar_zmod_n] using hodd
  simpa only [ZMod.card] using
    (quadratic_four_zero_count (F := ZMod q) (Ring.two_ne_zero hchar) a ha)

/-- A diagonal quadratic form in four variables over `ZMod q`, with all
coefficients nonzero and `q` odd, has a nontrivial zero. -/
theorem zmod_quadratic_four_nontrivial_zero (hodd : q ≠ 2)
    (a : Fin 4 → ZMod q) (ha : ∀ i, a i ≠ 0) :
    ∃ x : Fin 4 → ZMod q, (∑ i, a i * x i ^ 2 = 0) ∧ x ≠ 0 := by
  classical
  have hq : 3 ≤ q := by
    have hq2 := (Fact.out : q.Prime).two_le
    omega
  have hqZ : (3 : ℤ) ≤ q := by exact_mod_cast hq
  have hprod : (∏ i, a i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (by intro i _; exact ha i)
  have hchar : -1 ≤ quadraticChar (ZMod q) (∏ i, a i) := by
    rcases quadraticChar_dichotomy hprod with h | h <;> omega
  have hcount := zmod_quadratic_four_zero_count hodd a ha
  have hpos : (0 : ℤ) < ((q : ℤ) - 1) * ((q : ℤ) ^ 2 + 1) := by
    apply mul_pos <;> nlinarith
  have hmul : (0 : ℤ) ≤
      (((q : ℤ) - 1) * (q : ℤ)) *
        (quadraticChar (ZMod q) (∏ i, a i) + 1) :=
    mul_nonneg (mul_nonneg (by omega) (by omega)) (by omega)
  have hbig : 1 <
      (Fintype.card {x : Fin 4 → ZMod q // ∑ i, a i * x i ^ 2 = 0} : ℤ) := by
    nlinarith [hcount, hpos, hmul]
  have hbigNat : 1 <
      Fintype.card {x : Fin 4 → ZMod q // ∑ i, a i * x i ^ 2 = 0} := by
    exact_mod_cast hbig
  by_contra! h
  have hsub : Subsingleton {x : Fin 4 → ZMod q // ∑ i, a i * x i ^ 2 = 0} :=
    ⟨fun x y => Subtype.ext ((h x.1 x.2).trans (h y.1 y.2).symm)⟩
  have hle := Fintype.card_le_one_iff_subsingleton.mpr hsub
  omega

end ZMod

end Erdos940.Quartic
