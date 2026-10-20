module

public import Erdos940.Cubic.LocalCubic
public import Erdos940.Cubic.FixedParts
public import Erdos940.Cubic.PrimeSupply
public import Mathlib.Data.Nat.ChineseRemainder

/-!
# The modulus in the cube-full sum argument

For each of finitely many good primes, choose a noncube target and use the
Chinese remainder theorem to combine those targets into one progression.
-/

@[expose] public section

namespace Erdos940

open scoped Function

/-- A residue that is not a cube. This version does not require a field
instance, so it can be stated uniformly for varying prime moduli. -/
def IsNoncubeMod (q : ℕ) (u : ZMod q) : Prop :=
  ¬ ∃ x : ZMod q, x ^ 3 = u

/-- The product of the selected rational primes. -/
def goodModulus (Q : Finset ℕ) : ℕ := Q.prod id

theorem goodModulus_pos {D Q : Finset ℕ}
    (hQ : ∀ q ∈ Q, GoodPrime D q) : 0 < goodModulus Q := by
  unfold goodModulus
  exact Finset.prod_pos fun q hq => (hQ q hq).1.pos

/-- A field of prime order congruent to one modulo three has a noncube.
This uses the index-three subgroup of cubes in its cyclic unit group. -/
theorem exists_noncube_zmod (q : ℕ) (hq : q.Prime) (hmod : q % 3 = 1) :
    ∃ u : ZMod q, IsNoncubeMod q u := by
  letI : Fact q.Prime := ⟨hq⟩
  let H : Subgroup (ZMod q)ˣ := (powMonoidHom 3 : (ZMod q)ˣ →* (ZMod q)ˣ).range
  have hdiv : 3 ∣ Nat.card (ZMod q)ˣ := by
    rw [Nat.card_units, Nat.card_eq_fintype_card, ZMod.card]
    apply Nat.dvd_iff_mod_eq_zero.mpr
    omega
  have hindex : H.index = 3 := by
    dsimp [H]
    rw [IsCyclic.index_powMonoidHom_range, Nat.gcd_eq_right_iff_dvd]
    exact hdiv
  have hproper : H ≠ ⊤ := by
    intro heq
    rw [heq, Subgroup.index_top] at hindex
    omega
  obtain ⟨u, hu⟩ : ∃ u : (ZMod q)ˣ, u ∉ H := by
    by_contra h
    push_neg at h
    apply hproper
    ext u
    simp [h u]
  refine ⟨(u : ZMod q), ?_⟩
  intro ⟨x, hx⟩
  have hx0 : x ≠ 0 := by
    intro hxzero
    apply Units.ne_zero u
    simpa [hxzero] using hx.symm
  let ux : (ZMod q)ˣ := (isUnit_iff_ne_zero.mpr hx0).unit
  have hux : (ux : ZMod q) = x := IsUnit.unit_spec _
  have heq : ux ^ 3 = u := by
    apply Units.ext
    simpa [hux] using hx
  exact hu ⟨ux, by simpa only [powMonoidHom_apply] using heq⟩

/-- Chinese remainder selection of a progression whose target is a noncube
at every prime in `Q`. Finset membership ensures the primes are distinct. -/
theorem exists_good_noncube_progression {D Q : Finset ℕ}
    (hQ : ∀ q ∈ Q, GoodPrime D q) :
    ∃ a : ℕ, a < goodModulus Q ∧
      ∀ q ∈ Q, IsNoncubeMod q (a : ZMod q) := by
  classical
  have htargets : ∀ q : Q, ∃ u : ZMod q.1, IsNoncubeMod q.1 u := by
    intro q
    exact exists_noncube_zmod q.1 (hQ q.1 q.2).1 (hQ q.1 q.2).2.1
  choose u hu using htargets
  let residues : Q → ℕ := fun q => (u q).val
  let primes : Q → ℕ := fun q => q.1
  have hnonzero : ∀ q ∈ (Finset.univ : Finset Q), primes q ≠ 0 := by
    intro q _
    exact (hQ q.1 q.2).1.ne_zero
  have hcoprime : Set.Pairwise (Finset.univ : Finset Q)
      (Nat.Coprime on primes) := by
    intro p _ r _ hpr
    have hp : p.1.Prime := (hQ p.1 p.2).1
    have hr : r.1.Prime := (hQ r.1 r.2).1
    have hpne : p.1 ≠ r.1 := fun h => hpr (Subtype.ext h)
    exact (hp.coprime_iff_not_dvd).mpr
      (fun hdvd => hpne ((Nat.prime_dvd_prime_iff_eq hp hr).mp hdvd))
  let z := Nat.chineseRemainderOfFinset residues primes
    (Finset.univ : Finset Q) hnonzero hcoprime
  have hprod : (∏ q ∈ (Finset.univ : Finset Q), primes q) = goodModulus Q := by
    calc
      (∏ q ∈ (Finset.univ : Finset Q), primes q) =
          ∏ q ∈ Q.attach, q.1 := by simp [primes]
      _ = goodModulus Q := by
        simpa only [goodModulus, id_eq] using (Finset.prod_attach Q id)
  refine ⟨z.1, ?_, ?_⟩
  · have hz := Nat.chineseRemainderOfFinset_lt_prod residues primes
      (t := (Finset.univ : Finset Q)) hnonzero hcoprime
    exact hprod ▸ hz
  · intro q hq
    letI : NeZero q := ⟨(hQ q hq).1.ne_zero⟩
    let q' : Q := ⟨q, hq⟩
    have hmod : z.1 ≡ residues q' [MOD primes q'] := z.2 q' (Finset.mem_univ _)
    have hcast : (z.1 : ZMod q) = u q' := by
      have hcast' : (z.1 : ZMod q) = ((u q').val : ZMod q) :=
        (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
      simpa only [ZMod.natCast_zmod_val] using hcast'
    exact hcast ▸ hu q'

/-- At a prime modulus, the fixed-parts residue count is exactly the local
cubic count with those parts as coefficients. -/
theorem localCount_eq_localCubicCount_at_prime
    (q : ℕ) [Fact q.Prime] (d : Fin 3 → ℕ) (a : ℕ) :
    @localCount d q a ⟨(Fact.out : q.Prime).ne_zero⟩ =
      localCubicCount (ZMod q) (a : ZMod q) (fun i => (d i : ZMod q)) := by
  classical
  simp only [localCount, localCubicCount, cubeFormMod]
  rfl

/-- Each good prime saves at least `2q` solutions against the trivial `q²`
bound for a noncube target and a retained coefficient triple. -/
theorem goodPrime_localCount_bound {D : Finset ℕ} {q : ℕ}
    (hq : GoodPrime D q) (d : Fin 3 → ℕ) (hd : ∀ i, d i ∈ D)
    (a : ℕ) (ha : IsNoncubeMod q (a : ZMod q)) :
    @localCount d q a ⟨hq.1.ne_zero⟩ + 2 * q ≤ q * q := by
  letI : Fact q.Prime := ⟨hq.1⟩
  have hcoeff : ∀ i, ∃ b : ZMod q, b ≠ 0 ∧ b ^ 3 = (d i : ZMod q) := by
    intro i
    exact hq.2.2 (d i) (hd i)
  rw [localCount_eq_localCubicCount_at_prime q d a,
    localCubicCount_eq_threeCubesCount_of_cube_coefficients
      (ZMod q) (a : ZMod q) (fun i => (d i : ZMod q)) hcoeff]
  exact threeCubesCount_noncube_bound q hq.2.1 (a : ZMod q) ha

/-- A total version of `localCount`, defined at positive moduli. The value at
zero is irrelevant here; every modulus selected below is prime. -/
noncomputable def localCountAtModulus (d : Fin 3 → ℕ) (M a : ℕ) : ℕ :=
  if h : M ≠ 0 then @localCount d M a ⟨h⟩ else 0

theorem localCountAtModulus_eq {d : Fin 3 → ℕ} {M a : ℕ} (hM : M ≠ 0) :
    localCountAtModulus d M a = @localCount d M a ⟨hM⟩ := by
  simp [localCountAtModulus, hM]

/-- The Chinese remainder theorem decomposes the solutions of the cubic
congruence modulo a product of distinct primes into independent solutions at
each prime. -/
theorem localCount_goodModulus_eq_prod {D Q : Finset ℕ}
    (hQ : ∀ q ∈ Q, GoodPrime D q) (d : Fin 3 → ℕ) (a : ℕ) :
    @localCount d (goodModulus Q) a ⟨(goodModulus_pos hQ).ne'⟩ =
      ∏ q ∈ Q, localCountAtModulus d q a := by
  classical
  induction Q using Finset.induction_on with
  | empty =>
      simp only [goodModulus, Finset.prod_empty, localCount]
      have hnonempty : Nonempty
          {x : Fin 3 → ZMod 1 // cubeFormMod 1 d x = (a : ZMod 1)} :=
        ⟨⟨fun _ => 0, Subsingleton.elim _ _⟩⟩
      have hsub : Subsingleton
          {x : Fin 3 → ZMod 1 // cubeFormMod 1 d x = (a : ZMod 1)} := inferInstance
      exact Fintype.card_eq_one_iff.mpr
        ⟨hnonempty.some, fun y => Subsingleton.elim y hnonempty.some⟩
  | @insert q s hnot ih =>
      have hq : GoodPrime D q := hQ q (Finset.mem_insert_self q s)
      have hs : ∀ r ∈ s, GoodPrime D r := by
        intro r hr
        exact hQ r (Finset.mem_insert_of_mem hr)
      have hcoprime : q.Coprime (goodModulus s) := by
        apply (Nat.coprime_prod_right_iff).2
        intro r hr
        have hqr : q ≠ r := fun heq => hnot (heq ▸ hr)
        exact (hq.1.coprime_iff_not_dvd).2
          (fun hdvd => hqr ((Nat.prime_dvd_prime_iff_eq hq.1 (hs r hr).1).1 hdvd))
      have hM : goodModulus (insert q s) = q * goodModulus s := by
        simp [goodModulus, hnot]
      haveI : NeZero q := ⟨hq.1.ne_zero⟩
      haveI : NeZero (goodModulus s) := ⟨(goodModulus_pos hs).ne'⟩
      haveI : NeZero (q * goodModulus s) := ⟨mul_ne_zero hq.1.ne_zero
        (goodModulus_pos hs).ne'⟩
      haveI : NeZero (goodModulus (insert q s)) :=
        ⟨(goodModulus_pos hQ).ne'⟩
      have hfactor := localCount_mul_of_coprime d q (goodModulus s) a hcoprime
      calc
        localCount d (goodModulus (insert q s)) a =
            localCountAtModulus d (goodModulus (insert q s)) a :=
          (localCountAtModulus_eq (goodModulus_pos hQ).ne').symm
        _ = localCountAtModulus d (q * goodModulus s) a := by rw [hM]
        _ = localCount d (q * goodModulus s) a :=
          localCountAtModulus_eq (mul_ne_zero hq.1.ne_zero
            (goodModulus_pos hs).ne')
        _ = localCount d q a * localCount d (goodModulus s) a := hfactor
        _ = localCountAtModulus d q a *
              ∏ r ∈ s, localCountAtModulus d r a := by
            rw [localCountAtModulus_eq hq.1.ne_zero, ih hs]
        _ = ∏ r ∈ insert q s, localCountAtModulus d r a := by
            rw [Finset.prod_insert hnot]

end Erdos940
