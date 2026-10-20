import Erdos940.Quartic.FixedParts

/-!
# Chinese-remainder products of quartic local counts

For a finite family of positive pairwise-coprime moduli, the fixed-coefficient
quartic solution count factors into its local counts. Its normalization by the
fourth power of the product modulus is a product of local density factors,
with one remaining factor of the modulus in the denominator.
-/

namespace Erdos940.Quartic

open Finset

/-- The product of a finite set of moduli. -/
def quarticModulus (Q : Finset ℕ) : ℕ := Q.prod id

theorem quarticModulus_pos {Q : Finset ℕ}
    (hQ : ∀ q ∈ Q, 0 < q) : 0 < quarticModulus Q := by
  unfold quarticModulus
  exact Finset.prod_pos hQ

/-- The local count made total at modulus zero, which never occurs in the
applications below. -/
noncomputable def localCountAtModulus (d : Fin 4 → ℕ) (M a : ℕ) : ℕ :=
  if h : M ≠ 0 then @localCount d M a ⟨h⟩ else 0

theorem localCountAtModulus_eq {d : Fin 4 → ℕ} {M a : ℕ} (hM : M ≠ 0) :
    localCountAtModulus d M a = @localCount d M a ⟨hM⟩ := by
  simp [localCountAtModulus, hM]

/-- Independent congruence conditions factor the quartic local count. -/
theorem localCount_quarticModulus_eq_prod {Q : Finset ℕ}
    (hQ : ∀ q ∈ Q, 0 < q)
    (hcoprime : ∀ q ∈ Q, ∀ r ∈ Q, q ≠ r → q.Coprime r)
    (d : Fin 4 → ℕ) (a : ℕ) :
    @localCount d (quarticModulus Q) a ⟨(quarticModulus_pos hQ).ne'⟩ =
      ∏ q ∈ Q, localCountAtModulus d q a := by
  classical
  induction Q using Finset.induction_on with
  | empty =>
      simp only [quarticModulus, Finset.prod_empty, localCount]
      have hnonempty : Nonempty
          {x : Fin 4 → ZMod 1 // quarticFormMod 1 d x = (a : ZMod 1)} :=
        ⟨⟨fun _ => 0, Subsingleton.elim _ _⟩⟩
      have hsub : Subsingleton
          {x : Fin 4 → ZMod 1 // quarticFormMod 1 d x = (a : ZMod 1)} :=
        inferInstance
      exact Fintype.card_eq_one_iff.mpr
        ⟨hnonempty.some, fun y => Subsingleton.elim y hnonempty.some⟩
  | @insert q s hnot ih =>
      have hq : 0 < q := hQ q (Finset.mem_insert_self q s)
      have hs : ∀ r ∈ s, 0 < r := by
        intro r hr
        exact hQ r (Finset.mem_insert_of_mem hr)
      have hpair : ∀ r ∈ s, ∀ t ∈ s, r ≠ t → r.Coprime t := by
        intro r hr t ht hne
        exact hcoprime r (Finset.mem_insert_of_mem hr)
          t (Finset.mem_insert_of_mem ht) hne
      have hcop : q.Coprime (quarticModulus s) := by
        apply (Nat.coprime_prod_right_iff).2
        intro r hr
        have hne : q ≠ r := by
          intro heq
          exact hnot (heq ▸ hr)
        exact hcoprime q (Finset.mem_insert_self q s)
          r (Finset.mem_insert_of_mem hr) hne
      have hM : quarticModulus (insert q s) = q * quarticModulus s := by
        simp [quarticModulus, hnot]
      haveI : NeZero q := ⟨hq.ne'⟩
      haveI : NeZero (quarticModulus s) := ⟨(quarticModulus_pos hs).ne'⟩
      haveI : NeZero (q * quarticModulus s) :=
        ⟨mul_ne_zero hq.ne' (quarticModulus_pos hs).ne'⟩
      haveI : NeZero (quarticModulus (insert q s)) :=
        ⟨(quarticModulus_pos hQ).ne'⟩
      have hfactor := localCount_mul_of_coprime d q (quarticModulus s) a hcop
      calc
        localCount d (quarticModulus (insert q s)) a =
            localCountAtModulus d (quarticModulus (insert q s)) a :=
          (localCountAtModulus_eq (quarticModulus_pos hQ).ne').symm
        _ = localCountAtModulus d (q * quarticModulus s) a := by rw [hM]
        _ = localCount d (q * quarticModulus s) a :=
          localCountAtModulus_eq
            (mul_ne_zero hq.ne' (quarticModulus_pos hs).ne')
        _ = localCount d q a * localCount d (quarticModulus s) a := hfactor
        _ = localCountAtModulus d q a *
              ∏ r ∈ s, localCountAtModulus d r a := by
            rw [localCountAtModulus_eq hq.ne', ih hs hpair]
        _ = ∏ r ∈ insert q s, localCountAtModulus d r a := by
            rw [Finset.prod_insert hnot]

/-- The local density factor after removing the expected three powers of
the modulus from the four-variable solution count. -/
noncomputable def localDensityFactor (q : ℕ) (d : Fin 4 → ℕ) (a : ℕ) : ℝ :=
  (localCountAtModulus d q a : ℝ) / (q : ℝ) ^ 3

theorem localDensityFactor_nonneg (q : ℕ) (d : Fin 4 → ℕ) (a : ℕ) :
    0 ≤ localDensityFactor q d a := by
  unfold localDensityFactor
  positivity

/-- Normalize the CRT count by `M⁴`: the product of density factors carries
three powers of each modulus, leaving one further factor `M`. -/
theorem localCount_div_fourth_eq_localDensity_product_div
    {Q : Finset ℕ} (hQ : ∀ q ∈ Q, 0 < q)
    (hcoprime : ∀ q ∈ Q, ∀ r ∈ Q, q ≠ r → q.Coprime r)
    (d : Fin 4 → ℕ) (a : ℕ) :
    ((@localCount d (quarticModulus Q) a ⟨(quarticModulus_pos hQ).ne'⟩ : ℝ) /
        (quarticModulus Q : ℝ) ^ 4) =
      (∏ q ∈ Q, localDensityFactor q d a) /
        (quarticModulus Q : ℝ) := by
  have hM : (quarticModulus Q : ℝ) = ∏ q ∈ Q, (q : ℝ) := by
    simp [quarticModulus]
  have hcount :
      (@localCount d (quarticModulus Q) a ⟨(quarticModulus_pos hQ).ne'⟩ : ℝ) =
        ∏ q ∈ Q, (localCountAtModulus d q a : ℝ) := by
    exact_mod_cast localCount_quarticModulus_eq_prod hQ hcoprime d a
  have hfactors :
      (∏ q ∈ Q, localDensityFactor q d a) =
        (@localCount d (quarticModulus Q) a
          ⟨(quarticModulus_pos hQ).ne'⟩ : ℝ) /
          (quarticModulus Q : ℝ) ^ 3 := by
    simp_rw [localDensityFactor]
    rw [Finset.prod_div_distrib, Finset.prod_pow, ← hcount, hM]
  rw [hfactors]
  have hMne : (quarticModulus Q : ℝ) ≠ 0 := by
    exact_mod_cast (quarticModulus_pos hQ).ne'
  field_simp

end Erdos940.Quartic
