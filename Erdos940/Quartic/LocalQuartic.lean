import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Ring

/-!
# Elementary local bounds for four fourth powers

This file begins the local calculation in the quartic complement proof.
The coefficient-independent bound below is the finite-field ingredient of
the valuation-one `p²` estimate; it is not the character-sum estimate for
unit coefficients.
-/

namespace Erdos940.Quartic

/-- The number of solutions of a diagonal quartic equation over a finite field. -/
noncomputable def localQuarticCount (F : Type*) [Field F] [Fintype F]
    (u : F) (a : Fin 4 → F) : ℕ := by
  classical
  exact Fintype.card {x : Fin 4 → F // ∑ i, a i * x i ^ 4 = u}

/-- A quartic equation has at most four solutions in one variable. -/
theorem quarticFiber_card_le_four (F : Type*) [Field F] [Fintype F] (u : F) :
    Nat.card {x : F // x ^ 4 = u} ≤ 4 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hroots :
      (Finset.univ.filter fun x : F => x ^ 4 = u).val ⊆
        ((Polynomial.X : Polynomial F) ^ 4 - Polynomial.C u).roots := by
    intro x hx
    have hx' : x ^ 4 = u := by
      simpa only [Finset.mem_val, Finset.mem_filter, Finset.mem_univ, true_and] using hx
    exact (Polynomial.mem_roots_sub_C (by simp)).2 (by simpa using hx')
  simpa only [Polynomial.natDegree_X_pow_sub_C] using
    Polynomial.card_le_degree_of_subset_roots hroots

private theorem localQuarticCount_zero_coefficients
    (F : Type*) [Field F] [Fintype F] (u : F) (hu : u ≠ 0) :
    localQuarticCount F u (fun _ => 0) = 0 := by
  classical
  change Fintype.card {x : Fin 4 → F // ∑ i, (0 : F) * x i ^ 4 = u} = 0
  apply Fintype.card_eq_zero_iff.mpr
  refine ⟨fun x => ?_⟩
  have hx : (0 : F) = u := by simpa using x.2
  exact (Ne.symm hu) hx

theorem localQuarticCount_le_four_cube_of_nonzero_coefficient
    (F : Type*) [Field F] [Fintype F] (u : F) (a : Fin 4 → F)
    (i : Fin 4) (hi : a i ≠ 0) :
    localQuarticCount F u a ≤ 4 * (Fintype.card F) ^ 3 := by
  classical
  let e : F × (Fin 3 → F) ≃ (Fin 4 → F) :=
    Fin.insertNthEquiv (fun _ => F) i
  let k (y : Fin 3 → F) : F :=
    ∑ j, a (i.succAbove j) * y j ^ 4
  have hsum (p : F × (Fin 3 → F)) :
      (∑ j, a j * (e p j) ^ 4) = a i * p.1 ^ 4 + k p.2 := by
    rw [Fin.sum_univ_succAbove _ i]
    simp [e, k]
  let S : Finset (F × (Fin 3 → F)) :=
    Finset.univ.filter fun p => (∑ j, a j * (e p j) ^ 4) = u
  have hcount : localQuarticCount F u a = S.card := by
    unfold localQuarticCount
    calc
      Fintype.card {x : Fin 4 → F // ∑ j, a j * x j ^ 4 = u} =
          Fintype.card {p : F × (Fin 3 → F) // ∑ j, a j * (e p j) ^ 4 = u} :=
        Fintype.card_congr ((e.subtypeEquiv (fun _ => Iff.rfl)).symm)
      _ = S.card := by
        simpa [S] using
          (Fintype.card_subtype
            (fun p : F × (Fin 3 → F) => (∑ j, a j * (e p j) ^ 4) = u))
  have hroot (y : Fin 3 → F) :
      (Finset.univ.filter fun z : F => a i * z ^ 4 + k y = u).card ≤ 4 := by
    let v : F := (u - k y) / a i
    have heq (z : F) : a i * z ^ 4 + k y = u ↔ z ^ 4 = v := by
      dsimp [v]
      constructor
      · intro hz
        apply (eq_div_iff hi).2
        calc
          z ^ 4 * a i = a i * z ^ 4 := mul_comm _ _
          _ = u - k y := eq_sub_iff_add_eq.mpr hz
      · intro hz
        have hz' : z ^ 4 * a i = u - k y := (eq_div_iff hi).1 hz
        apply eq_sub_iff_add_eq.mp
        simpa only [mul_comm] using hz'
    have hset :
        (Finset.univ.filter fun z : F => a i * z ^ 4 + k y = u) =
          (Finset.univ.filter fun z : F => z ^ 4 = v) := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact heq z
    rw [hset]
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using
      quarticFiber_card_le_four F v
  have hfiber (y : Fin 3 → F) :
      (S.filter fun p => p.2 = y).card ≤ 4 := by
    let T : Finset F := Finset.univ.filter fun z => a i * z ^ 4 + k y = u
    calc
      (S.filter fun p => p.2 = y).card ≤ T.card := by
        apply Finset.card_le_card_of_injOn (f := Prod.fst)
        · intro p hp
          obtain ⟨hpS, hpy⟩ := Finset.mem_filter.mp hp
          have hpEq := (Finset.mem_filter.mp hpS).2
          rw [hsum p] at hpEq
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, by simpa only [hpy] using hpEq⟩
        · intro p hp p' hp' hfst
          have hpy := (Finset.mem_filter.mp hp).2
          have hpy' := (Finset.mem_filter.mp hp').2
          exact Prod.ext hfst (hpy.trans hpy'.symm)
      _ ≤ 4 := hroot y
  have hS : S.card ≤ 4 * Fintype.card (Fin 3 → F) := by
    calc
      S.card ≤ 4 * (Finset.univ : Finset (Fin 3 → F)).card :=
        Finset.card_le_mul_card_image_of_maps_to
          (f := fun p : F × (Fin 3 → F) => p.2) (s := S) (t := Finset.univ)
          (by intro p _; exact Finset.mem_univ _) 4
          (by intro y _; exact hfiber y)
      _ = 4 * Fintype.card (Fin 3 → F) := by simp
  calc
    localQuarticCount F u a = S.card := hcount
    _ ≤ 4 * Fintype.card (Fin 3 → F) := hS
    _ = 4 * (Fintype.card F) ^ 3 := by simp

/-- The coefficient-independent root bound at a nonzero target. -/
theorem localQuarticCount_le_four_cube
    (F : Type*) [Field F] [Fintype F] (u : F) (hu : u ≠ 0)
    (a : Fin 4 → F) :
    localQuarticCount F u a ≤ 4 * (Fintype.card F) ^ 3 := by
  classical
  by_cases h : ∃ i, a i ≠ 0
  · obtain ⟨i, hi⟩ := h
    exact localQuarticCount_le_four_cube_of_nonzero_coefficient F u a i hi
  · have ha : a = fun _ => 0 := by
      funext i
      exact not_not.mp (not_exists.mp h i)
    rw [ha, localQuarticCount_zero_coefficients F u hu]
    simp

/-- With unit coefficients in characteristic other than two, every nonzero
vector is a nonsingular point of the diagonal quartic hypersurface. -/
theorem quartic_derivative_nonzero_of_nonzero_vector
    (F : Type*) [Field F] (a x : Fin 4 → F)
    (hfour : (4 : F) ≠ 0) (ha : ∀ i, a i ≠ 0)
    (hx : x ≠ fun _ => 0) :
    ∃ i, 4 * a i * x i ^ 3 ≠ 0 := by
  by_contra h
  push Not at h
  apply hx
  funext i
  have hzero := h i
  rcases mul_eq_zero.mp hzero with hleft | hpow
  · exact False.elim (mul_ne_zero hfour (ha i) hleft)
  · exact eq_zero_of_pow_eq_zero hpow

/-- A nontrivial linear equation in four variables over a finite field has
exactly `|F|³` solutions. -/
theorem linearFiber_card_eq_cube (F : Type*) [Field F] [Fintype F]
    (c : Fin 4 → F) (u : F) (i : Fin 4) (hi : c i ≠ 0) :
    Nat.card {x : Fin 4 → F // ∑ j, c j * x j = u} = (Fintype.card F) ^ 3 := by
  classical
  let e : F × (Fin 3 → F) ≃ (Fin 4 → F) :=
    Fin.insertNthEquiv (fun _ => F) i
  let k (y : Fin 3 → F) : F := ∑ j, c (i.succAbove j) * y j
  have hsum (z : F) (y : Fin 3 → F) :
      (∑ j, c j * e (z, y) j) = c i * z + k y := by
    rw [Fin.sum_univ_succAbove _ i]
    simp [e, k]
  let E : (Fin 3 → F) ≃ {x : Fin 4 → F // ∑ j, c j * x j = u} :=
    { toFun := fun y => ⟨e ((u - k y) / c i, y), by
        rw [hsum]
        field_simp
        ring⟩
      invFun := fun x => (e.symm x.val).2
      left_inv := by
        intro y
        simp
      right_inv := by
        intro x
        apply Subtype.ext
        let z := (e.symm x.val).1
        let y := (e.symm x.val).2
        have hx : c i * z + k y = u := by
          simpa [z, y, ← hsum, e.apply_symm_apply] using x.property
        have hz : (u - k y) / c i = z := by
          apply (div_eq_iff hi).2
          calc
            u - k y = c i * z := by linear_combination hx.symm
            _ = z * c i := mul_comm _ _
        change e ((u - k y) / c i, y) = x.val
        rw [hz]
        exact e.apply_symm_apply x.val }
  calc
    Nat.card {x : Fin 4 → F // ∑ j, c j * x j = u} =
        Nat.card (Fin 3 → F) := (Nat.card_congr E).symm
    _ = (Fintype.card F) ^ 3 := by simp

/-- The first-order quartic expansion over a ring in which the increment is
square-zero. This is the algebraic step in lifting a nonsingular root from
modulo `p` to modulo `p²`. -/
theorem quartic_add_sq_zero {R : Type*} [CommRing R] (x h : R) (hh : h ^ 2 = 0) :
    (x + h) ^ 4 = x ^ 4 + 4 * x ^ 3 * h := by
  calc
    (x + h) ^ 4 = x ^ 4 + 4 * x ^ 3 * h +
        h ^ 2 * (6 * x ^ 2 + 4 * x * h + h ^ 2) := by ring
    _ = x ^ 4 + 4 * x ^ 3 * h := by simp [hh]

/-- Multiples of `p` square to zero modulo `p²`. -/
theorem zmod_prime_square_shift_sq_zero (p : ℕ) (t : ZMod (p ^ 2)) :
    ((p : ZMod (p ^ 2)) * t) ^ 2 = 0 := by
  rw [mul_pow, ← Nat.cast_pow, ZMod.natCast_self]
  simp

/-- An explicit Hensel linearization of the quartic monomial modulo `p²`. -/
theorem zmod_prime_square_quartic_shift (p : ℕ) (x t : ZMod (p ^ 2)) :
    (x + (p : ZMod (p ^ 2)) * t) ^ 4 =
      x ^ 4 + (p : ZMod (p ^ 2)) * (4 * x ^ 3 * t) := by
  rw [quartic_add_sq_zero x _ (zmod_prime_square_shift_sq_zero p t)]
  ring

/-- The full diagonal form linearizes coordinatewise modulo `p²`. -/
theorem zmod_prime_square_quartic_form_shift (p : ℕ)
    (a x t : Fin 4 → ZMod (p ^ 2)) :
    (∑ i, a i * (x i + (p : ZMod (p ^ 2)) * t i) ^ 4) =
      (∑ i, a i * x i ^ 4) +
        (p : ZMod (p ^ 2)) * (∑ i, 4 * a i * x i ^ 3 * t i) := by
  simp_rw [zmod_prime_square_quartic_shift]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Reduction of the quartic form commutes with coefficient and variable
reduction. -/
theorem zmod_prime_square_quartic_form_cast (p : ℕ)
    (a x : Fin 4 → ZMod (p ^ 2)) :
    (ZMod.cast (∑ i, a i * x i ^ 4) : ZMod p) =
      ∑ i, (ZMod.cast (a i) : ZMod p) * (ZMod.cast (x i) : ZMod p) ^ 4 := by
  change (ZMod.castHom (show p ∣ p ^ 2 by simp) (ZMod p) :
      ZMod (p ^ 2) →+* ZMod p) (∑ i, a i * x i ^ 4) = _
  rw [map_sum]
  congr 1
  ext i
  simp only [map_mul, map_pow, ZMod.castHom_apply]

/-- The kernel of reduction from `p²` to `p` consists exactly of multiples of
`p`. This is the divisibility input for valuation-one lifting. -/
theorem zmod_prime_square_cast_eq_zero_iff (p : ℕ) (hp : p.Prime)
    (x : ZMod (p ^ 2)) :
    (ZMod.cast x : ZMod p) = 0 ↔
      ∃ t : ZMod (p ^ 2), x = (p : ZMod (p ^ 2)) * t := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  constructor
  · intro hx
    rw [ZMod.cast_eq_val] at hx
    have hdiv : p ∣ x.val := (ZMod.natCast_eq_zero_iff x.val p).mp hx
    obtain ⟨t, ht⟩ := hdiv
    refine ⟨(t : ZMod (p ^ 2)), ?_⟩
    calc
      x = (x.val : ZMod (p ^ 2)) := (ZMod.natCast_zmod_val x).symm
      _ = (p : ZMod (p ^ 2)) * t := by rw [ht, Nat.cast_mul]
  · rintro ⟨t, rfl⟩
    rw [ZMod.cast_mul (show p ∣ p ^ 2 by simp)]
    simp

/-- The valuation-one target `p` is nonzero modulo `p²`. -/
theorem zmod_prime_square_prime_ne_zero (p : ℕ) (hp : p.Prime) :
    (p : ZMod (p ^ 2)) ≠ 0 := by
  intro h
  have hlt : p < p ^ 2 := by
    calc
      p = p * 1 := by omega
      _ < p * p := Nat.mul_lt_mul_of_pos_left hp.one_lt hp.pos
      _ = p ^ 2 := by ring
  exact (Nat.not_dvd_of_pos_of_lt hp.pos hlt)
    ((ZMod.natCast_eq_zero_iff p (p ^ 2)).mp h)

/-- Cancellation by `p` modulo `p²` is reduction modulo `p`. -/
theorem zmod_prime_square_mul_prime_eq_zero_iff (p : ℕ) (hp : p.Prime)
    (x : ZMod (p ^ 2)) :
    (p : ZMod (p ^ 2)) * x = 0 ↔ (ZMod.cast x : ZMod p) = 0 := by
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hrepr : (p : ZMod (p ^ 2)) * x = ((p * x.val : ℕ) : ZMod (p ^ 2)) := by
    calc
      (p : ZMod (p ^ 2)) * x = (p : ZMod (p ^ 2)) * (x.val : ZMod (p ^ 2)) := by
        rw [ZMod.natCast_zmod_val]
      _ = ((p * x.val : ℕ) : ZMod (p ^ 2)) := by rw [Nat.cast_mul]
  calc
    (p : ZMod (p ^ 2)) * x = 0 ↔ p * p ∣ p * x.val := by
      rw [hrepr, ← pow_two]
      exact ZMod.natCast_eq_zero_iff (p * x.val) (p ^ 2)
    _ ↔ p ∣ x.val := Nat.mul_dvd_mul_iff_left hp.pos
    _ ↔ (ZMod.cast x : ZMod p) = 0 := by
      rw [ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff]

/-- Multiplication by `p` identifies the residue field with the reduction
kernel modulo `p²`. -/
noncomputable def zmodPrimeSquareKernelEquiv (p : ℕ) (hp : p.Prime) :
    ZMod p ≃ {x : ZMod (p ^ 2) // (ZMod.cast x : ZMod p) = 0} := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let φ : ZMod p → {x : ZMod (p ^ 2) // (ZMod.cast x : ZMod p) = 0} :=
    fun t => ⟨(p : ZMod (p ^ 2)) * (t.val : ZMod (p ^ 2)),
      (zmod_prime_square_mul_prime_eq_zero_iff p hp _).mp (by
        calc
          (p : ZMod (p ^ 2)) * ((p : ZMod (p ^ 2)) * (t.val : ZMod (p ^ 2))) =
              (p : ZMod (p ^ 2)) ^ 2 * (t.val : ZMod (p ^ 2)) := by ring
          _ = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self, zero_mul])⟩
  have hinj : Function.Injective φ := by
    intro t u htu
    have heq : (p : ZMod (p ^ 2)) * (t.val : ZMod (p ^ 2)) =
        (p : ZMod (p ^ 2)) * (u.val : ZMod (p ^ 2)) := congrArg Subtype.val htu
    have hzero : (p : ZMod (p ^ 2)) *
        ((t.val : ZMod (p ^ 2)) - (u.val : ZMod (p ^ 2))) = 0 := by
      rw [mul_sub, heq, sub_self]
    have hred := (zmod_prime_square_mul_prime_eq_zero_iff p hp _).mp hzero
    rw [ZMod.cast_sub (show p ∣ p ^ 2 by simp)] at hred
    simpa only [ZMod.cast_natCast (show p ∣ p ^ 2 by simp),
      ZMod.natCast_zmod_val, sub_eq_zero] using hred
  have hsurj : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    obtain ⟨s, hs⟩ := (zmod_prime_square_cast_eq_zero_iff p hp x).mp hx
    let t : ZMod p := ZMod.cast s
    have hred : (ZMod.cast (s - (t.val : ZMod (p ^ 2))) : ZMod p) = 0 := by
      rw [ZMod.cast_sub (show p ∣ p ^ 2 by simp)]
      rw [ZMod.cast_natCast (show p ∣ p ^ 2 by simp)]
      rw [ZMod.natCast_zmod_val]
      simp [t]
    have hzero := (zmod_prime_square_mul_prime_eq_zero_iff p hp _).mpr hred
    have heq : (p : ZMod (p ^ 2)) * s =
        (p : ZMod (p ^ 2)) * (t.val : ZMod (p ^ 2)) := by
      rwa [mul_sub, sub_eq_zero] at hzero
    refine ⟨t, Subtype.ext ?_⟩
    exact (hs.trans heq).symm
  exact Equiv.ofBijective φ ⟨hinj, hsurj⟩

theorem zmodPrimeSquareKernelEquiv_apply (p : ℕ) (hp : p.Prime) (t : ZMod p) :
    (zmodPrimeSquareKernelEquiv p hp t).val =
      (p : ZMod (p ^ 2)) * (t.val : ZMod (p ^ 2)) := rfl

/-- A chosen lift of a residue gives a coordinatewise parametrization of all
other lifts by one digit modulo `p`. -/
noncomputable def zmodPrimeSquareFiberEquiv (p : ℕ) (hp : p.Prime)
    (b : ZMod (p ^ 2)) :
    ZMod p ≃ {x : ZMod (p ^ 2) // (ZMod.cast x : ZMod p) = ZMod.cast b} := by
  classical
  let e : ZMod (p ^ 2) ≃ ZMod (p ^ 2) := Equiv.addRight b
  have he (z : ZMod (p ^ 2)) :
      (ZMod.cast z : ZMod p) = 0 ↔ (ZMod.cast (e z) : ZMod p) = ZMod.cast b := by
    change (ZMod.cast z : ZMod p) = 0 ↔ (ZMod.cast (z + b) : ZMod p) = ZMod.cast b
    rw [ZMod.cast_add (show p ∣ p ^ 2 by simp)]
    simp
  exact (zmodPrimeSquareKernelEquiv p hp).trans (e.subtypeEquiv he)

theorem zmodPrimeSquareFiberEquiv_apply (p : ℕ) (hp : p.Prime)
    (b : ZMod (p ^ 2)) (t : ZMod p) :
    (zmodPrimeSquareFiberEquiv p hp b t).val =
      b + (p : ZMod (p ^ 2)) * (t.val : ZMod (p ^ 2)) := by
  unfold zmodPrimeSquareFiberEquiv
  change (zmodPrimeSquareKernelEquiv p hp t).val + b = _
  rw [zmodPrimeSquareKernelEquiv_apply]
  ring

/-- Four independent residue digits parametrize the lifts of a vector. -/
noncomputable def zmodPrimeSquareVectorFiberEquiv (p : ℕ) (hp : p.Prime)
    (b : Fin 4 → ZMod (p ^ 2)) :
    (Fin 4 → ZMod p) ≃ {x : Fin 4 → ZMod (p ^ 2) //
      ∀ i, (ZMod.cast (x i) : ZMod p) = ZMod.cast (b i)} :=
  (Equiv.piCongrRight (fun i => zmodPrimeSquareFiberEquiv p hp (b i))).trans
    (Equiv.subtypePiEquivPi
      (p := fun i (z : ZMod (p ^ 2)) =>
        (ZMod.cast z : ZMod p) = ZMod.cast (b i))).symm

theorem zmodPrimeSquareVectorFiberEquiv_apply (p : ℕ) (hp : p.Prime)
    (b : Fin 4 → ZMod (p ^ 2)) (t : Fin 4 → ZMod p) (i : Fin 4) :
    (zmodPrimeSquareVectorFiberEquiv p hp b t).val i =
      b i + (p : ZMod (p ^ 2)) * (t i).val := by
  exact zmodPrimeSquareFiberEquiv_apply p hp (b i) (t i)

/-- A fixed coordinatewise section of reduction from `p²` to `p`. -/
noncomputable def zmodPrimeSquareVectorLift (p : ℕ) (_hp : p.Prime)
    (y : Fin 4 → ZMod p) : Fin 4 → ZMod (p ^ 2) :=
  fun i => Classical.choose
    (ZMod.castHom_surjective (show p ∣ p ^ 2 by simp) (y i))

theorem zmodPrimeSquareVectorLift_cast (p : ℕ) (hp : p.Prime)
    (y : Fin 4 → ZMod p) (i : Fin 4) :
    (ZMod.cast (zmodPrimeSquareVectorLift p hp y i) : ZMod p) = y i :=
  Classical.choose_spec
    (ZMod.castHom_surjective (show p ∣ p ^ 2 by simp) (y i))

theorem zmod_prime_square_reduction_kernel_card (p : ℕ) (hp : p.Prime) :
    Nat.card {x : ZMod (p ^ 2) // (ZMod.cast x : ZMod p) = 0} = p := by
  calc
    Nat.card {x : ZMod (p ^ 2) // (ZMod.cast x : ZMod p) = 0} =
        Nat.card (ZMod p) := (Nat.card_congr (zmodPrimeSquareKernelEquiv p hp)).symm
    _ = p := by simp

/-- Every residue modulo `p` has exactly `p` lifts modulo `p²`. -/
theorem zmod_prime_square_reduction_fiber_card (p : ℕ) (hp : p.Prime)
    (y : ZMod p) :
    Nat.card {x : ZMod (p ^ 2) // (ZMod.cast x : ZMod p) = y} = p := by
  obtain ⟨a, ha⟩ := ZMod.castHom_surjective (show p ∣ p ^ 2 by simp) y
  change (ZMod.cast a : ZMod p) = y at ha
  let e : ZMod (p ^ 2) ≃ ZMod (p ^ 2) := Equiv.addRight a
  have he (z : ZMod (p ^ 2)) :
      (ZMod.cast z : ZMod p) = 0 ↔ (ZMod.cast (e z) : ZMod p) = y := by
    change (ZMod.cast z : ZMod p) = 0 ↔ (ZMod.cast (z + a) : ZMod p) = y
    rw [ZMod.cast_add (show p ∣ p ^ 2 by simp), ha]
    simp
  let E : {z : ZMod (p ^ 2) // (ZMod.cast z : ZMod p) = 0} ≃
      {z : ZMod (p ^ 2) // (ZMod.cast z : ZMod p) = y} :=
    e.subtypeEquiv he
  calc
    Nat.card {z : ZMod (p ^ 2) // (ZMod.cast z : ZMod p) = y} =
        Nat.card {z : ZMod (p ^ 2) // (ZMod.cast z : ZMod p) = 0} :=
      (Nat.card_congr E).symm
    _ = p := zmod_prime_square_reduction_kernel_card p hp

/-- A four-coordinate residue vector has exactly `p⁴` lifts modulo `p²`. -/
theorem zmod_prime_square_vector_reduction_fiber_card (p : ℕ) (hp : p.Prime)
    (y : Fin 4 → ZMod p) :
    Nat.card {x : Fin 4 → ZMod (p ^ 2) //
      ∀ i, (ZMod.cast (x i) : ZMod p) = y i} = p ^ 4 := by
  classical
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  calc
    Nat.card {x : Fin 4 → ZMod (p ^ 2) //
        ∀ i, (ZMod.cast (x i) : ZMod p) = y i} =
        Nat.card (∀ i : Fin 4,
          {z : ZMod (p ^ 2) // (ZMod.cast z : ZMod p) = y i}) :=
      Nat.card_congr (Equiv.subtypePiEquivPi
        (p := fun i (z : ZMod (p ^ 2)) => (ZMod.cast z : ZMod p) = y i))
    _ = ∏ i : Fin 4,
        Nat.card {z : ZMod (p ^ 2) // (ZMod.cast z : ZMod p) = y i} := by
      simp [Nat.card_eq_fintype_card]
    _ = p ^ 4 := by
      simp only [zmod_prime_square_reduction_fiber_card p hp]
      simp

/-- A coordinate divisible by `p` has vanishing fourth power modulo `p²`. -/
theorem zmod_prime_square_quartic_eq_zero_of_cast_eq_zero (p : ℕ) (hp : p.Prime)
    (x : ZMod (p ^ 2)) (hx : (ZMod.cast x : ZMod p) = 0) : x ^ 4 = 0 := by
  obtain ⟨t, rfl⟩ := (zmod_prime_square_cast_eq_zero_iff p hp x).mp hx
  rw [show 4 = 2 * 2 by decide, pow_mul, zmod_prime_square_shift_sq_zero]
  simp

/-- A valuation-one target forces a unit coefficient and a unit coordinate,
provided coefficients divisible by `p` already vanish modulo `p²`. -/
theorem zmod_prime_square_quartic_unit_coordinate (p : ℕ) (hp : p.Prime)
    (a x : Fin 4 → ZMod (p ^ 2))
    (ha : ∀ i, (ZMod.cast (a i) : ZMod p) = 0 → a i = 0)
    (hsol : (∑ i, a i * x i ^ 4) = (p : ZMod (p ^ 2))) :
    ∃ i, (ZMod.cast (a i) : ZMod p) ≠ 0 ∧
      (ZMod.cast (x i) : ZMod p) ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have hterm (i : Fin 4) : a i * x i ^ 4 = 0 := by
    by_cases hai : (ZMod.cast (a i) : ZMod p) = 0
    · simp [ha i hai]
    · simp [zmod_prime_square_quartic_eq_zero_of_cast_eq_zero p hp (x i) (h i hai)]
  have hzero : (∑ i, a i * x i ^ 4) = 0 := by simp [hterm]
  exact (zmod_prime_square_prime_ne_zero p hp) (hsol.symm.trans hzero)

/-- The unit-coordinate criterion for integer coefficients whose positive
`p`-adic valuations are at least two (in particular, canonical quartic parts). -/
theorem zmod_prime_square_quartic_unit_coordinate_nat (p : ℕ) (hp : p.Prime)
    (d : Fin 4 → ℕ) (x : Fin 4 → ZMod (p ^ 2))
    (hd : ∀ i, p ∣ d i → p ^ 2 ∣ d i)
    (hsol : (∑ i, (d i : ZMod (p ^ 2)) * x i ^ 4) = (p : ZMod (p ^ 2))) :
    ∃ i, (d i : ZMod p) ≠ 0 ∧ (ZMod.cast (x i) : ZMod p) ≠ 0 := by
  have ha (i : Fin 4) (hi : (ZMod.cast (d i : ZMod (p ^ 2)) : ZMod p) = 0) :
      (d i : ZMod (p ^ 2)) = 0 := by
    rw [ZMod.cast_natCast (show p ∣ p ^ 2 by simp)] at hi
    exact (ZMod.natCast_eq_zero_iff (d i) (p ^ 2)).mpr
      (hd i ((ZMod.natCast_eq_zero_iff (d i) p).mp hi))
  obtain ⟨i, hi, hxi⟩ :=
    zmod_prime_square_quartic_unit_coordinate p hp (fun i => (d i : ZMod (p ^ 2)))
      x ha hsol
  refine ⟨i, ?_, hxi⟩
  simpa only [ZMod.cast_natCast (show p ∣ p ^ 2 by simp)] using hi

/-- The all-zero residue vector never lifts to the valuation-one target `p`.
This is the exceptional fiber subtracted in equation (13). -/
theorem zmod_prime_square_zero_vector_no_lift (p : ℕ) (hp : p.Prime)
    (a x : Fin 4 → ZMod (p ^ 2))
    (hx : ∀ i, (ZMod.cast (x i) : ZMod p) = 0) :
    (∑ i, a i * x i ^ 4) ≠ (p : ZMod (p ^ 2)) := by
  have hzero : (∑ i, a i * x i ^ 4) = 0 := by
    simp [zmod_prime_square_quartic_eq_zero_of_cast_eq_zero p hp, hx]
  rw [hzero]
  exact Ne.symm (zmod_prime_square_prime_ne_zero p hp)

/-- A nonsingular quartic zero modulo `p` lifts to a solution with target `p`
modulo `p²` by changing just one coordinate by a multiple of `p`. -/
theorem zmod_prime_square_quartic_lift_to_prime (p : ℕ) (hp : p.Prime)
    (a x : Fin 4 → ZMod (p ^ 2)) (i : Fin 4)
    (hbase : (ZMod.cast (∑ j, a j * x j ^ 4) : ZMod p) = 0)
    (hderiv : (ZMod.cast (4 * a i * x i ^ 3) : ZMod p) ≠ 0) :
    ∃ t : ZMod (p ^ 2),
      (∑ j, a j * (x j + (p : ZMod (p ^ 2)) *
        (if j = i then t else 0)) ^ 4) = (p : ZMod (p ^ 2)) := by
  letI : Fact p.Prime := ⟨hp⟩
  let d : ZMod (p ^ 2) := 4 * a i * x i ^ 3
  let v : ZMod (p ^ 2) := ∑ j, a j * x j ^ 4
  have hdelta : (ZMod.cast ((p : ZMod (p ^ 2)) - v) : ZMod p) = 0 := by
    rw [ZMod.cast_sub (show p ∣ p ^ 2 by simp)]
    simp [v, hbase]
  obtain ⟨s, hs⟩ :=
    (zmod_prime_square_cast_eq_zero_iff p hp ((p : ZMod (p ^ 2)) - v)).mp hdelta
  let r : ZMod p := (ZMod.cast s : ZMod p) / (ZMod.cast d : ZMod p)
  obtain ⟨t, ht⟩ :=
    ZMod.castHom_surjective (show p ∣ p ^ 2 by simp) r
  change (ZMod.cast t : ZMod p) = r at ht
  have hlin : (ZMod.cast (d * t) : ZMod p) = (ZMod.cast s : ZMod p) := by
    rw [ZMod.cast_mul (show p ∣ p ^ 2 by simp)]
    change (ZMod.cast d : ZMod p) * (ZMod.cast t : ZMod p) = _
    rw [ht]
    dsimp [r]
    exact mul_div_cancel₀ _ (by simpa [d] using hderiv)
  have hmul : (p : ZMod (p ^ 2)) * (d * t) = (p : ZMod (p ^ 2)) * s := by
    have hz : (ZMod.cast (d * t - s) : ZMod p) = 0 := by
      rw [ZMod.cast_sub (show p ∣ p ^ 2 by simp), hlin, sub_self]
    have hz' := (zmod_prime_square_mul_prime_eq_zero_iff p hp (d * t - s)).mpr hz
    calc
      (p : ZMod (p ^ 2)) * (d * t) =
          (p : ZMod (p ^ 2)) * s + (p : ZMod (p ^ 2)) * (d * t - s) := by ring
      _ = (p : ZMod (p ^ 2)) * s := by rw [hz']; ring
  refine ⟨t, ?_⟩
  rw [zmod_prime_square_quartic_form_shift p a x
    (fun j => if j = i then t else 0)]
  have hsum : (∑ j, 4 * a j * x j ^ 3 * (if j = i then t else 0)) = d * t := by
    simp [d]
  rw [hsum, hmul]
  change v + (p : ZMod (p ^ 2)) * s = (p : ZMod (p ^ 2))
  rw [← hs]
  ring

/-- Each nonsingular zero modulo `p` has exactly `p³` lifts solving the
valuation-one quartic equation modulo `p²`. The base point `b` is any chosen
lift of that residue vector. -/
theorem zmod_prime_square_quartic_nonsingular_lift_card (p : ℕ) (hp : p.Prime)
    (a b : Fin 4 → ZMod (p ^ 2)) (i : Fin 4)
    (hbase : (ZMod.cast (∑ j, a j * b j ^ 4) : ZMod p) = 0)
    (hderiv : (ZMod.cast (4 * a i * b i ^ 3) : ZMod p) ≠ 0) :
    Nat.card {x : Fin 4 → ZMod (p ^ 2) //
      (∀ j, (ZMod.cast (x j) : ZMod p) = ZMod.cast (b j)) ∧
      (∑ j, a j * x j ^ 4) = (p : ZMod (p ^ 2))} = p ^ 3 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let v : ZMod (p ^ 2) := ∑ j, a j * b j ^ 4
  have hdelta : (ZMod.cast ((p : ZMod (p ^ 2)) - v) : ZMod p) = 0 := by
    rw [ZMod.cast_sub (show p ∣ p ^ 2 by simp)]
    simp [v, hbase]
  obtain ⟨s, hs⟩ :=
    (zmod_prime_square_cast_eq_zero_iff p hp ((p : ZMod (p ^ 2)) - v)).mp hdelta
  let c : Fin 4 → ZMod p := fun j => ZMod.cast (4 * a j * b j ^ 3)
  have hci : c i ≠ 0 := hderiv
  let L (t : Fin 4 → ZMod p) : ZMod (p ^ 2) :=
    ∑ j, 4 * a j * b j ^ 3 * ((t j).val : ZMod (p ^ 2))
  have hform (t : Fin 4 → ZMod p) :
      (∑ j, a j * (zmodPrimeSquareVectorFiberEquiv p hp b t).val j ^ 4) =
        v + (p : ZMod (p ^ 2)) * L t := by
    simp_rw [zmodPrimeSquareVectorFiberEquiv_apply]
    exact zmod_prime_square_quartic_form_shift p a b
      (fun j => ((t j).val : ZMod (p ^ 2)))
  have htarget : v + (p : ZMod (p ^ 2)) * s = p := by
    rw [← hs]
    ring
  have hcast (t : Fin 4 → ZMod p) :
      (ZMod.cast (L t) : ZMod p) = ∑ j, c j * t j := by
    dsimp [L, c]
    change (ZMod.castHom (show p ∣ p ^ 2 by simp) (ZMod p) :
        ZMod (p ^ 2) →+* ZMod p)
      (∑ j, 4 * a j * b j ^ 3 * ((t j).val : ZMod (p ^ 2))) =
        ∑ j, (ZMod.cast (4 * a j * b j ^ 3) : ZMod p) * t j
    rw [map_sum]
    congr 1
    ext j
    simp only [map_mul, ZMod.castHom_apply,
      ZMod.cast_natCast (show p ∣ p ^ 2 by simp), ZMod.natCast_zmod_val]
    simp only [ZMod.cast_mul (show p ∣ p ^ 2 by simp)]
  have heq (t : Fin 4 → ZMod p) :
      (∑ j, a j * (zmodPrimeSquareVectorFiberEquiv p hp b t).val j ^ 4) =
        (p : ZMod (p ^ 2)) ↔ ∑ j, c j * t j = ZMod.cast s := by
    rw [hform]
    have hiff : v + (p : ZMod (p ^ 2)) * L t = p ↔
        (p : ZMod (p ^ 2)) * (L t - s) = 0 := by
      constructor
      · intro h
        calc
          (p : ZMod (p ^ 2)) * (L t - s) =
              (v + (p : ZMod (p ^ 2)) * L t) -
                (v + (p : ZMod (p ^ 2)) * s) := by ring
          _ = 0 := by rw [h, htarget, sub_self]
      · intro h
        calc
          v + (p : ZMod (p ^ 2)) * L t =
              (v + (p : ZMod (p ^ 2)) * s) +
                (p : ZMod (p ^ 2)) * (L t - s) := by ring
          _ = p := by rw [htarget, h, add_zero]
    rw [hiff, zmod_prime_square_mul_prime_eq_zero_iff p hp]
    rw [ZMod.cast_sub (show p ∣ p ^ 2 by simp), sub_eq_zero, hcast]
  let E := zmodPrimeSquareVectorFiberEquiv p hp b
  let E' : {t : Fin 4 → ZMod p // ∑ j, c j * t j = ZMod.cast s} ≃
      {x : Fin 4 → ZMod (p ^ 2) //
        (∀ j, (ZMod.cast (x j) : ZMod p) = ZMod.cast (b j)) ∧
        (∑ j, a j * x j ^ 4) = (p : ZMod (p ^ 2))} :=
    (E.subtypeEquiv (fun t => (heq t).symm)).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter
        (p := fun x : Fin 4 → ZMod (p ^ 2) =>
          ∀ j, (ZMod.cast (x j) : ZMod p) = ZMod.cast (b j))
        (q := fun x : Fin 4 → ZMod (p ^ 2) =>
          (∑ j, a j * x j ^ 4) = (p : ZMod (p ^ 2))))
  calc
    Nat.card {x : Fin 4 → ZMod (p ^ 2) //
        (∀ j, (ZMod.cast (x j) : ZMod p) = ZMod.cast (b j)) ∧
        (∑ j, a j * x j ^ 4) = (p : ZMod (p ^ 2))} =
      Nat.card {t : Fin 4 → ZMod p // ∑ j, c j * t j = ZMod.cast s} :=
        (Nat.card_congr E').symm
    _ = (Fintype.card (ZMod p)) ^ 3 := linearFiber_card_eq_cube _ c _ i hci
    _ = p ^ 3 := by simp

/-- The exact lift count indexed by the residue vector. -/
theorem zmod_prime_square_quartic_residue_lift_card (p : ℕ) (hp : p.Prime)
    (a : Fin 4 → ZMod (p ^ 2)) (y : Fin 4 → ZMod p) (i : Fin 4)
    (hy : (∑ j, (ZMod.cast (a j) : ZMod p) * y j ^ 4) = 0)
    (hi : (4 : ZMod p) * (ZMod.cast (a i) : ZMod p) * y i ^ 3 ≠ 0) :
    Nat.card {x : Fin 4 → ZMod (p ^ 2) //
      (∀ j, (ZMod.cast (x j) : ZMod p) = y j) ∧
      (∑ j, a j * x j ^ 4) = (p : ZMod (p ^ 2))} = p ^ 3 := by
  classical
  let b := zmodPrimeSquareVectorLift p hp y
  have hb (j : Fin 4) : (ZMod.cast (b j) : ZMod p) = y j :=
    zmodPrimeSquareVectorLift_cast p hp y j
  have hbase : (ZMod.cast (∑ j, a j * b j ^ 4) : ZMod p) = 0 := by
    rw [zmod_prime_square_quartic_form_cast]
    simpa only [hb] using hy
  have h4 : (ZMod.cast (4 : ZMod (p ^ 2)) : ZMod p) = 4 := by
    exact ZMod.cast_natCast (show p ∣ p ^ 2 by simp) 4
  have hderiv : (ZMod.cast (4 * a i * b i ^ 3) : ZMod p) ≠ 0 := by
    simpa only [ZMod.cast_mul (show p ∣ p ^ 2 by simp),
      ZMod.cast_pow (show p ∣ p ^ 2 by simp),
      h4, hb i] using hi
  let E : {x : Fin 4 → ZMod (p ^ 2) //
      (∀ j, (ZMod.cast (x j) : ZMod p) = y j) ∧
      (∑ j, a j * x j ^ 4) = (p : ZMod (p ^ 2))} ≃
      {x : Fin 4 → ZMod (p ^ 2) //
      (∀ j, (ZMod.cast (x j) : ZMod p) = ZMod.cast (b j)) ∧
      (∑ j, a j * x j ^ 4) = (p : ZMod (p ^ 2))} :=
    (Equiv.refl _).subtypeEquiv (fun x => by simp [hb])
  calc
    Nat.card {x : Fin 4 → ZMod (p ^ 2) //
        (∀ j, (ZMod.cast (x j) : ZMod p) = y j) ∧
        (∑ j, a j * x j ^ 4) = (p : ZMod (p ^ 2))} =
      Nat.card {x : Fin 4 → ZMod (p ^ 2) //
        (∀ j, (ZMod.cast (x j) : ZMod p) = ZMod.cast (b j)) ∧
        (∑ j, a j * x j ^ 4) = (p : ZMod (p ^ 2))} := Nat.card_congr E
    _ = p ^ 3 := zmod_prime_square_quartic_nonsingular_lift_card p hp a b i
      hbase hderiv

/-- Partition the solutions modulo `p²` according to their residue vectors. -/
theorem zmod_prime_square_quartic_count_eq_sum_residue_fibers (p : ℕ) [NeZero p]
    (a : Fin 4 → ZMod (p ^ 2)) :
    Nat.card {x : Fin 4 → ZMod (p ^ 2) //
      (∑ j, a j * x j ^ 4) = (p : ZMod (p ^ 2))} =
      ∑ y : Fin 4 → ZMod p,
        Nat.card {x : Fin 4 → ZMod (p ^ 2) //
          (∀ j, (ZMod.cast (x j) : ZMod p) = y j) ∧
          (∑ j, a j * x j ^ 4) = (p : ZMod (p ^ 2))} := by
  classical
  let S := {x : Fin 4 → ZMod (p ^ 2) //
      (∑ j, a j * x j ^ 4) = (p : ZMod (p ^ 2))}
  let f : S → (Fin 4 → ZMod p) := fun x j => ZMod.cast (x.val j)
  let E : S ≃ Σ y : Fin 4 → ZMod p, {z : S // f z = y} :=
    (Equiv.sigmaFiberEquiv f).symm
  have hfiber (y : Fin 4 → ZMod p) :
      Nat.card {z : S // f z = y} =
        Nat.card {x : Fin 4 → ZMod (p ^ 2) //
          (∀ j, (ZMod.cast (x j) : ZMod p) = y j) ∧
          (∑ j, a j * x j ^ 4) = (p : ZMod (p ^ 2))} := by
    let e : {z : S // f z = y} ≃
        {x : Fin 4 → ZMod (p ^ 2) //
          (∀ j, (ZMod.cast (x j) : ZMod p) = y j) ∧
          (∑ j, a j * x j ^ 4) = (p : ZMod (p ^ 2))} :=
      { toFun := fun z => ⟨z.val.val, ⟨congrFun z.property, z.val.property⟩⟩
        invFun := fun z => ⟨⟨z.val, z.property.2⟩, funext z.property.1⟩
        left_inv := by intro z; cases z; rfl
        right_inv := by intro z; cases z; rfl }
    exact Nat.card_congr e
  calc
    Nat.card S = Nat.card (Σ y : Fin 4 → ZMod p, {z : S // f z = y}) :=
      Nat.card_congr E
    _ = ∑ y : Fin 4 → ZMod p, Nat.card {z : S // f z = y} := by
      simp only [Nat.card_eq_fintype_card, Fintype.card_sigma]
    _ = ∑ y : Fin 4 → ZMod p,
        Nat.card {x : Fin 4 → ZMod (p ^ 2) //
          (∀ j, (ZMod.cast (x j) : ZMod p) = y j) ∧
          (∑ j, a j * x j ^ 4) = (p : ZMod (p ^ 2))} := by
      apply Finset.sum_congr rfl
      intro y _
      exact hfiber y

/-- Under the canonical valuation condition, every nonempty valuation-one
fiber is nonsingular and consequently has exactly `p³` points. -/
theorem zmod_prime_square_quartic_residue_fiber_card_le (p : ℕ) (hp : p.Prime)
    (a : Fin 4 → ZMod (p ^ 2))
    (ha : ∀ i, (ZMod.cast (a i) : ZMod p) = 0 → a i = 0)
    (hfour : (4 : ZMod p) ≠ 0) (y : Fin 4 → ZMod p) :
    Nat.card {x : Fin 4 → ZMod (p ^ 2) //
      (∀ j, (ZMod.cast (x j) : ZMod p) = y j) ∧
      (∑ j, a j * x j ^ 4) = (p : ZMod (p ^ 2))} ≤ p ^ 3 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let T := {x : Fin 4 → ZMod (p ^ 2) //
      (∀ j, (ZMod.cast (x j) : ZMod p) = y j) ∧
      (∑ j, a j * x j ^ 4) = (p : ZMod (p ^ 2))}
  by_cases hT : Nonempty T
  · obtain ⟨x⟩ := hT
    obtain ⟨i, hai, hxi⟩ := zmod_prime_square_quartic_unit_coordinate
      p hp a x.val ha x.property.2
    have hyi : y i ≠ 0 := by simpa only [x.property.1 i] using hxi
    have hroot : (∑ j, (ZMod.cast (a j) : ZMod p) * y j ^ 4) = 0 := by
      have hcast := congrArg
        (ZMod.castHom (show p ∣ p ^ 2 by simp) (ZMod p)) x.property.2
      change (ZMod.cast (∑ j, a j * x.val j ^ 4) : ZMod p) =
        ZMod.cast (p : ZMod (p ^ 2)) at hcast
      rw [zmod_prime_square_quartic_form_cast] at hcast
      have hpzero : (ZMod.cast (p : ZMod (p ^ 2)) : ZMod p) = 0 := by
        rw [ZMod.cast_natCast (show p ∣ p ^ 2 by simp)]
        exact ZMod.natCast_self p
      rw [hpzero] at hcast
      simpa only [x.property.1] using hcast
    have hderiv : (4 : ZMod p) * (ZMod.cast (a i) : ZMod p) * y i ^ 3 ≠ 0 :=
      mul_ne_zero (mul_ne_zero hfour hai) (pow_ne_zero 3 hyi)
    exact le_of_eq (zmod_prime_square_quartic_residue_lift_card p hp a y i
      hroot hderiv)
  · have hzero : Nat.card T = 0 := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_eq_zero_iff.mpr ⟨fun x => hT ⟨x⟩⟩
    change Nat.card T ≤ p ^ 3
    rw [hzero]
    exact Nat.zero_le _

/-- The valuation-one count is bounded by `p³` times the number of quartic
zeros modulo `p`. -/
theorem zmod_prime_square_quartic_count_le_prime_zero_count (p : ℕ) (hp : p.Prime)
    [Fact p.Prime]
    (a : Fin 4 → ZMod (p ^ 2))
    (ha : ∀ i, (ZMod.cast (a i) : ZMod p) = 0 → a i = 0)
    (hfour : (4 : ZMod p) ≠ 0) :
    Nat.card {x : Fin 4 → ZMod (p ^ 2) //
      (∑ j, a j * x j ^ 4) = (p : ZMod (p ^ 2))} ≤
      localQuarticCount (ZMod p) 0 (fun i => ZMod.cast (a i)) * p ^ 3 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let a₀ : Fin 4 → ZMod p := fun i => ZMod.cast (a i)
  let root (y : Fin 4 → ZMod p) : Prop := (∑ j, a₀ j * y j ^ 4) = 0
  have hfiber (y : Fin 4 → ZMod p) :
      Nat.card {x : Fin 4 → ZMod (p ^ 2) //
        (∀ j, (ZMod.cast (x j) : ZMod p) = y j) ∧
        (∑ j, a j * x j ^ 4) = (p : ZMod (p ^ 2))} ≤
        if root y then p ^ 3 else 0 := by
    by_cases hy : root y
    · simpa [hy] using
        zmod_prime_square_quartic_residue_fiber_card_le p hp a ha hfour y
    · have hempty : IsEmpty {x : Fin 4 → ZMod (p ^ 2) //
          (∀ j, (ZMod.cast (x j) : ZMod p) = y j) ∧
          (∑ j, a j * x j ^ 4) = (p : ZMod (p ^ 2))} := by
        refine ⟨fun x => hy ?_⟩
        have hcast := congrArg
          (ZMod.castHom (show p ∣ p ^ 2 by simp) (ZMod p)) x.property.2
        change (ZMod.cast (∑ j, a j * x.val j ^ 4) : ZMod p) =
          ZMod.cast (p : ZMod (p ^ 2)) at hcast
        rw [zmod_prime_square_quartic_form_cast] at hcast
        have hpzero : (ZMod.cast (p : ZMod (p ^ 2)) : ZMod p) = 0 := by
          rw [ZMod.cast_natCast (show p ∣ p ^ 2 by simp)]
          exact ZMod.natCast_self p
        rw [hpzero] at hcast
        simpa only [root, a₀, x.property.1] using hcast
      have hzero : Nat.card {x : Fin 4 → ZMod (p ^ 2) //
          (∀ j, (ZMod.cast (x j) : ZMod p) = y j) ∧
          (∑ j, a j * x j ^ 4) = (p : ZMod (p ^ 2))} = 0 := by
        rw [Nat.card_eq_fintype_card]
        exact Fintype.card_eq_zero_iff.mpr hempty
      simp [hy, hzero]
  calc
    Nat.card {x : Fin 4 → ZMod (p ^ 2) //
        (∑ j, a j * x j ^ 4) = (p : ZMod (p ^ 2))} =
      ∑ y : Fin 4 → ZMod p,
        Nat.card {x : Fin 4 → ZMod (p ^ 2) //
          (∀ j, (ZMod.cast (x j) : ZMod p) = y j) ∧
          (∑ j, a j * x j ^ 4) = (p : ZMod (p ^ 2))} :=
      zmod_prime_square_quartic_count_eq_sum_residue_fibers p a
    _ ≤ ∑ y : Fin 4 → ZMod p, if root y then p ^ 3 else 0 := by
      apply Finset.sum_le_sum
      intro y _
      exact hfiber y
    _ = localQuarticCount (ZMod p) 0 a₀ * p ^ 3 := by
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const]
      simp [localQuarticCount, Fintype.card_subtype, root, a₀]

/-- Equation (14), in integral form: the normalized valuation-one local count
is at most four. -/
theorem zmod_prime_square_quartic_count_le_four_cube_square (p : ℕ)
    (hp : p.Prime) [Fact p.Prime] (a : Fin 4 → ZMod (p ^ 2))
    (ha : ∀ i, (ZMod.cast (a i) : ZMod p) = 0 → a i = 0)
    (hfour : (4 : ZMod p) ≠ 0) :
    Nat.card {x : Fin 4 → ZMod (p ^ 2) //
      (∑ j, a j * x j ^ 4) = (p : ZMod (p ^ 2))} ≤ 4 * p ^ 6 := by
  classical
  by_cases hcoeff : ∃ i, (ZMod.cast (a i) : ZMod p) ≠ 0
  · obtain ⟨i, hi⟩ := hcoeff
    have hzero := localQuarticCount_le_four_cube_of_nonzero_coefficient
      (ZMod p) 0 (fun j => ZMod.cast (a j)) i hi
    have hpCard : Fintype.card (ZMod p) = p := by simp
    rw [hpCard] at hzero
    calc
      Nat.card {x : Fin 4 → ZMod (p ^ 2) //
          (∑ j, a j * x j ^ 4) = (p : ZMod (p ^ 2))} ≤
        localQuarticCount (ZMod p) 0 (fun j => ZMod.cast (a j)) * p ^ 3 :=
        zmod_prime_square_quartic_count_le_prime_zero_count p hp a ha hfour
      _ ≤ (4 * p ^ 3) * p ^ 3 := Nat.mul_le_mul_right _ hzero
      _ = 4 * p ^ 6 := by ring
  · have hzero : a = fun _ => 0 := by
      funext i
      exact ha i (not_not.mp (not_exists.mp hcoeff i))
    have hempty : IsEmpty {x : Fin 4 → ZMod (p ^ 2) //
        (∑ j, a j * x j ^ 4) = (p : ZMod (p ^ 2))} := by
      refine ⟨fun x => ?_⟩
      have hx : (0 : ZMod (p ^ 2)) = p := by simpa [hzero] using x.property
      exact (zmod_prime_square_prime_ne_zero p hp) hx.symm
    have hcard : Nat.card {x : Fin 4 → ZMod (p ^ 2) //
        (∑ j, a j * x j ^ 4) = (p : ZMod (p ^ 2))} = 0 := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_eq_zero_iff.mpr hempty
    rw [hcard]
    exact Nat.zero_le _

/-- Equation (13) before replacing the nonzero-root count by the full root
count minus one. -/
theorem zmod_prime_square_quartic_count_eq_nonzero_roots_times_cube (p : ℕ)
    (hp : p.Prime) [Fact p.Prime] (a : Fin 4 → ZMod (p ^ 2))
    (ha : ∀ i, (ZMod.cast (a i) : ZMod p) ≠ 0)
    (hfour : (4 : ZMod p) ≠ 0) :
    Nat.card {x : Fin 4 → ZMod (p ^ 2) //
      (∑ j, a j * x j ^ 4) = (p : ZMod (p ^ 2))} =
      Nat.card {y : Fin 4 → ZMod p //
        (∑ j, (ZMod.cast (a j) : ZMod p) * y j ^ 4) = 0 ∧
        y ≠ fun _ => 0} * p ^ 3 := by
  classical
  let a₀ : Fin 4 → ZMod p := fun i => ZMod.cast (a i)
  let root (y : Fin 4 → ZMod p) : Prop := (∑ j, a₀ j * y j ^ 4) = 0
  let good (y : Fin 4 → ZMod p) : Prop := root y ∧ y ≠ fun _ => 0
  have hfiber (y : Fin 4 → ZMod p) :
      Nat.card {x : Fin 4 → ZMod (p ^ 2) //
        (∀ j, (ZMod.cast (x j) : ZMod p) = y j) ∧
        (∑ j, a j * x j ^ 4) = (p : ZMod (p ^ 2))} =
        if good y then p ^ 3 else 0 := by
    by_cases hgood : good y
    · have ⟨hy, hnonzero⟩ := hgood
      obtain ⟨i, hi⟩ := quartic_derivative_nonzero_of_nonzero_vector
        (ZMod p) a₀ y hfour ha hnonzero
      simpa [hgood] using
        zmod_prime_square_quartic_residue_lift_card p hp a y i hy hi
    · have hempty : IsEmpty {x : Fin 4 → ZMod (p ^ 2) //
          (∀ j, (ZMod.cast (x j) : ZMod p) = y j) ∧
          (∑ j, a j * x j ^ 4) = (p : ZMod (p ^ 2))} := by
        refine ⟨fun x => hgood ?_⟩
        have hcast := congrArg
          (ZMod.castHom (show p ∣ p ^ 2 by simp) (ZMod p)) x.property.2
        change (ZMod.cast (∑ j, a j * x.val j ^ 4) : ZMod p) =
          ZMod.cast (p : ZMod (p ^ 2)) at hcast
        rw [zmod_prime_square_quartic_form_cast] at hcast
        have hpzero : (ZMod.cast (p : ZMod (p ^ 2)) : ZMod p) = 0 := by
          rw [ZMod.cast_natCast (show p ∣ p ^ 2 by simp)]
          exact ZMod.natCast_self p
        rw [hpzero] at hcast
        have hroot : root y := by simpa only [root, a₀, x.property.1] using hcast
        have hnonzero : y ≠ fun _ => 0 := by
          intro hzero
          exact (zmod_prime_square_zero_vector_no_lift p hp a x.val
            (by intro j; rw [x.property.1 j, hzero])) x.property.2
        exact ⟨hroot, hnonzero⟩
      have hzero : Nat.card {x : Fin 4 → ZMod (p ^ 2) //
          (∀ j, (ZMod.cast (x j) : ZMod p) = y j) ∧
          (∑ j, a j * x j ^ 4) = (p : ZMod (p ^ 2))} = 0 := by
        rw [Nat.card_eq_fintype_card]
        exact Fintype.card_eq_zero_iff.mpr hempty
      simp [hgood, hzero]
  calc
    Nat.card {x : Fin 4 → ZMod (p ^ 2) //
        (∑ j, a j * x j ^ 4) = (p : ZMod (p ^ 2))} =
      ∑ y : Fin 4 → ZMod p,
        Nat.card {x : Fin 4 → ZMod (p ^ 2) //
          (∀ j, (ZMod.cast (x j) : ZMod p) = y j) ∧
          (∑ j, a j * x j ^ 4) = (p : ZMod (p ^ 2))} :=
      zmod_prime_square_quartic_count_eq_sum_residue_fibers p a
    _ = ∑ y : Fin 4 → ZMod p, if good y then p ^ 3 else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      exact hfiber y
    _ = Nat.card {y : Fin 4 → ZMod p // good y} * p ^ 3 := by
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const]
      simp [Nat.card_eq_fintype_card, Fintype.card_subtype]
    _ = Nat.card {y : Fin 4 → ZMod p //
        (∑ j, (ZMod.cast (a j) : ZMod p) * y j ^ 4) = 0 ∧
        y ≠ fun _ => 0} * p ^ 3 := rfl

/-- The zero vector is one of the quartic zeros, and every other zero is
counted in the punctured fiber. -/
theorem localQuarticCount_zero_eq_nonzero_plus_one
    (F : Type*) [Field F] [Fintype F] (a : Fin 4 → F) :
    Nat.card {y : Fin 4 → F // (∑ j, a j * y j ^ 4) = 0 ∧
      y ≠ fun _ => 0} + 1 = localQuarticCount F 0 a := by
  classical
  let R : Finset (Fin 4 → F) :=
    Finset.univ.filter fun y => (∑ j, a j * y j ^ 4) = 0
  have hzero : (fun _ : Fin 4 => (0 : F)) ∈ R := by simp [R]
  have hpunctured : Nat.card {y : Fin 4 → F //
      (∑ j, a j * y j ^ 4) = 0 ∧ y ≠ fun _ => 0} =
      (R.erase (fun _ => 0)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext y
    simp [R, Finset.mem_erase, and_comm]
  have hfull : localQuarticCount F 0 a = R.card := by
    simp [localQuarticCount, Fintype.card_subtype, R]
  rw [hpunctured, hfull]
  exact Finset.card_erase_add_one hzero

/-- Equation (13), in integral form. Dividing both sides by `p⁶` gives
`ρ_{p²}(p) = ρ_p(0) - p⁻³`. -/
theorem zmod_prime_square_quartic_count_eq_prime_zero_count_sub_one (p : ℕ)
    (hp : p.Prime) [Fact p.Prime] (a : Fin 4 → ZMod (p ^ 2))
    (ha : ∀ i, (ZMod.cast (a i) : ZMod p) ≠ 0)
    (hfour : (4 : ZMod p) ≠ 0) :
    Nat.card {x : Fin 4 → ZMod (p ^ 2) //
      (∑ j, a j * x j ^ 4) = (p : ZMod (p ^ 2))} =
      (localQuarticCount (ZMod p) 0 (fun i => ZMod.cast (a i)) - 1) * p ^ 3 := by
  have hcount := zmod_prime_square_quartic_count_eq_nonzero_roots_times_cube
    p hp a ha hfour
  have hroots := localQuarticCount_zero_eq_nonzero_plus_one
    (ZMod p) (fun i => ZMod.cast (a i))
  have hcard : Nat.card {y : Fin 4 → ZMod p //
      (∑ j, (ZMod.cast (a j) : ZMod p) * y j ^ 4) = 0 ∧
      y ≠ fun _ => 0} =
        localQuarticCount (ZMod p) 0 (fun i => ZMod.cast (a i)) - 1 := by
    omega
  rw [hcard] at hcount
  exact hcount

/-- The normalized identity `ρ_{p²}(p) = ρ_p(0) - p⁻³` for unit
coefficients, expressed directly in rational arithmetic. -/
theorem zmod_prime_square_quartic_density_eq_prime_zero_density_sub (p : ℕ)
    (hp : p.Prime) [Fact p.Prime] (a : Fin 4 → ZMod (p ^ 2))
    (ha : ∀ i, (ZMod.cast (a i) : ZMod p) ≠ 0)
    (hfour : (4 : ZMod p) ≠ 0) :
    (Nat.card {x : Fin 4 → ZMod (p ^ 2) //
      (∑ j, a j * x j ^ 4) = (p : ZMod (p ^ 2))} : ℚ) / (p : ℚ) ^ 6 =
      (localQuarticCount (ZMod p) 0 (fun i => ZMod.cast (a i)) : ℚ) /
        (p : ℚ) ^ 3 - 1 / (p : ℚ) ^ 3 := by
  let N := localQuarticCount (ZMod p) 0 (fun i => ZMod.cast (a i))
  let M := Nat.card {x : Fin 4 → ZMod (p ^ 2) //
    (∑ j, a j * x j ^ 4) = (p : ZMod (p ^ 2))}
  have hcount : M = (N - 1) * p ^ 3 :=
    zmod_prime_square_quartic_count_eq_prime_zero_count_sub_one p hp a ha hfour
  have hpos : 1 ≤ N := by
    have hroots := localQuarticCount_zero_eq_nonzero_plus_one
      (ZMod p) (fun i => ZMod.cast (a i))
    dsimp [N]
    omega
  have hnat : M + p ^ 3 = N * p ^ 3 := by
    rw [hcount]
    calc
      (N - 1) * p ^ 3 + p ^ 3 = ((N - 1) + 1) * p ^ 3 := by ring
      _ = N * p ^ 3 := by rw [Nat.sub_add_cancel hpos]
  have hq : (M : ℚ) + (p : ℚ) ^ 3 = (N : ℚ) * (p : ℚ) ^ 3 := by
    exact_mod_cast hnat
  have hpne : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  dsimp [M, N] at *
  field_simp
  nlinarith [hq]

/-- The rationally normalized form of equation (14). -/
theorem zmod_prime_square_quartic_density_le_four (p : ℕ)
    (hp : p.Prime) [Fact p.Prime] (a : Fin 4 → ZMod (p ^ 2))
    (ha : ∀ i, (ZMod.cast (a i) : ZMod p) = 0 → a i = 0)
    (hfour : (4 : ZMod p) ≠ 0) :
    (Nat.card {x : Fin 4 → ZMod (p ^ 2) //
      (∑ j, a j * x j ^ 4) = (p : ZMod (p ^ 2))} : ℚ) / (p : ℚ) ^ 6 ≤ 4 := by
  have hcount := zmod_prime_square_quartic_count_le_four_cube_square
    p hp a ha hfour
  have hpQ : (0 : ℚ) < p := by exact_mod_cast hp.pos
  have hp_pos : (0 : ℚ) < (p : ℚ) ^ 6 := by positivity
  apply (div_le_iff₀ hp_pos).2
  exact_mod_cast hcount

/-- A power permutation that turns fourth powers into squares.
The congruence assumptions on its exponent hold when the field size is `3 mod 4`. -/
theorem exists_quarticSquarePowerEquiv_of_exponent
    (F : Type*) [Field F] [Fintype F] (m : ℕ)
    (hm : 2 * m = Fintype.card F + 3)
    (hcop : (Fintype.card F - 1).Coprime m) :
    ∃ e : F ≃ F, ∀ x, (e x) ^ 2 = x ^ 4 := by
  classical
  have hcopUnits : (Nat.card Fˣ).Coprime m := by
    simpa [Nat.card_eq_fintype_card, Fintype.card_units] using hcop
  have hmpos : 0 < m := by omega
  have hinj : Function.Injective (fun x : F => x ^ m) := by
    intro x y hxy
    by_cases hx : x = 0
    · subst x
      have hy : y = 0 := by
        by_contra hy
        have hp : (0 : F) = y ^ m := by simpa [hmpos.ne'] using hxy
        exact (pow_ne_zero m hy) hp.symm
      exact hy.symm
    · have hy : y ≠ 0 := by
        intro hy
        have hp : x ^ m = (0 : F) := by simpa [hy, hmpos.ne'] using hxy
        exact (pow_ne_zero m hx) hp
      have hu : (Units.mk0 x hx : Fˣ) ^ m = (Units.mk0 y hy : Fˣ) ^ m := by
        apply Units.ext
        simpa using hxy
      have heq := (Nat.Coprime.pow_left_bijective hcopUnits).1 hu
      exact congrArg Units.val heq
  let e : F ≃ F := Equiv.ofBijective (fun x => x ^ m)
    ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩
  have hpow (x : F) : (e x) ^ 2 = x ^ 4 := by
    change (x ^ m) ^ 2 = x ^ 4
    rw [← pow_mul, show m * 2 = Fintype.card F + 3 by omega, pow_add,
      FiniteField.pow_card]
    ring
  exact ⟨e, hpow⟩

theorem quarticFiber_card_eq_squareFiber_card_of_exponent
    (F : Type*) [Field F] [Fintype F] (u : F) (m : ℕ)
    (hm : 2 * m = Fintype.card F + 3)
    (hcop : (Fintype.card F - 1).Coprime m) :
    Nat.card {x : F // x ^ 4 = u} = Nat.card {x : F // x ^ 2 = u} := by
  obtain ⟨e, hpow⟩ := exists_quarticSquarePowerEquiv_of_exponent F m hm hcop
  let fibers : {x : F // x ^ 4 = u} ≃ {x : F // x ^ 2 = u} :=
    e.subtypeEquiv (fun x => by rw [hpow x])
  exact Nat.card_congr fibers

/-- The power permutation for a finite field of cardinality `3 mod 4`. -/
theorem exists_quarticSquarePowerEquiv_of_mod_four_three
    (F : Type*) [Field F] [Fintype F]
    (hmod : Fintype.card F % 4 = 3) :
    ∃ e : F ≃ F, ∀ x, (e x) ^ 2 = x ^ 4 := by
  let k := Fintype.card F / 4
  let m := 2 * k + 3
  have hq : Fintype.card F = 4 * k + 3 := by
    dsimp [k]
    omega
  have hm : 2 * m = Fintype.card F + 3 := by
    dsimp [m]
    omega
  have hOddM : Odd m := ⟨k + 1, by dsimp [m]; omega⟩
  have hOddK : Odd (2 * k + 1) := ⟨k, by omega⟩
  have h1 : m.Coprime 2 := hOddM.coprime_two_right
  have hbase : (2 : ℕ).Coprime (2 * k + 1) := hOddK.coprime_two_left
  have h2 : m.Coprime (2 * k + 1) := by
    have h := (Nat.coprime_add_self_left).2 hbase
    convert h using 1; dsimp [m]; omega
  have hcop : (Fintype.card F - 1).Coprime m := by
    rw [hq, show 4 * k + 3 - 1 = 2 * (2 * k + 1) by omega]
    exact (h1.mul_right h2).symm
  exact exists_quarticSquarePowerEquiv_of_exponent F m hm hcop

/-- Over a finite field of cardinality `3 mod 4`, every target has the same
number of fourth roots as square roots. -/
theorem quarticFiber_card_eq_squareFiber_card_of_mod_four_three
    (F : Type*) [Field F] [Fintype F] (u : F)
    (hmod : Fintype.card F % 4 = 3) :
    Nat.card {x : F // x ^ 4 = u} = Nat.card {x : F // x ^ 2 = u} := by
  obtain ⟨e, hpow⟩ := exists_quarticSquarePowerEquiv_of_mod_four_three F hmod
  exact Nat.card_congr (e.subtypeEquiv (fun x => by rw [hpow x]))

/-- At primes `3 mod 4`, a diagonal quartic and the corresponding diagonal
quadratic form have exactly the same number of solutions at every target. -/
theorem localQuarticCount_eq_quadraticCount_of_mod_four_three
    (F : Type*) [Field F] [Fintype F] (u : F) (a : Fin 4 → F)
    (hmod : Fintype.card F % 4 = 3) :
    localQuarticCount F u a =
      Nat.card {x : Fin 4 → F // ∑ i, a i * x i ^ 2 = u} := by
  classical
  obtain ⟨e, hpow⟩ := exists_quarticSquarePowerEquiv_of_mod_four_three F hmod
  let E : (Fin 4 → F) ≃ (Fin 4 → F) := Equiv.piCongrRight (fun _ => e)
  have hE (x : Fin 4 → F) (i : Fin 4) : E x i = e (x i) := rfl
  let fibers : {x : Fin 4 → F // ∑ i, a i * x i ^ 4 = u} ≃
      {x : Fin 4 → F // ∑ i, a i * x i ^ 2 = u} :=
    E.subtypeEquiv (fun x => by simp only [hE, hpow])
  simpa only [localQuarticCount, Nat.card_eq_fintype_card] using
    Fintype.card_congr fibers

end Erdos940.Quartic
