import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Erdos940.Quartic.GaussianBoundary

/-!
# Signed square cells in the Gaussian lattice

Every integer lattice point lies in one square cell of side `q`.  The cell
indices are integers, so this partition covers all four quadrants without
separate sign cases.  The statements below concern finite sets and exact
reindexing, before any analytic estimate is applied.
-/

namespace Erdos940.Quartic.GaussianCellPartition

open Finset

/-- The integer point in signed cell `(i,j)` at offsets `(u,v)`. -/
def signedCellPoint (q : ℕ) (i j : ℤ) (u v : Fin q) : ℤ × ℤ :=
  (i * (q : ℤ) + (u : ℕ), j * (q : ℤ) + (v : ℕ))

/-- The unique signed square-cell index containing an integer point. -/
def cellIndex (q : ℕ) (p : ℤ × ℤ) : ℤ × ℤ :=
  (p.1 / (q : ℤ), p.2 / (q : ℤ))

/-- The coordinates inside a cell, represented by `Fin q`. -/
def cellOffset (q : ℕ) (hq : 0 < q) (p : ℤ × ℤ) : Fin q × Fin q :=
  (⟨(p.1 % (q : ℤ)).toNat, by
      have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
      have hqpos : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq
      have h0 := Int.emod_nonneg p.1 hq0
      have h1 := Int.emod_lt_of_pos p.1 hqpos
      omega⟩,
   ⟨(p.2 % (q : ℤ)).toNat, by
      have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
      have hqpos : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq
      have h0 := Int.emod_nonneg p.2 hq0
      have h1 := Int.emod_lt_of_pos p.2 hqpos
      omega⟩)

theorem signedCellPoint_cellIndex_cellOffset (q : ℕ) (hq : 0 < q)
    (p : ℤ × ℤ) :
    signedCellPoint q (cellIndex q p).1 (cellIndex q p).2
      (cellOffset q hq p).1 (cellOffset q hq p).2 = p := by
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have h1 : (p.1 % (q : ℤ)).toNat = p.1 % (q : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg p.1 hq0)
  have h2 : (p.2 % (q : ℤ)).toNat = p.2 % (q : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg p.2 hq0)
  apply Prod.ext
  · change p.1 / (q : ℤ) * (q : ℤ) +
      ((p.1 % (q : ℤ)).toNat : ℤ) = p.1
    rw [h1]
    simpa only [mul_comm, add_comm] using Int.emod_add_mul_ediv p.1 (q : ℤ)
  · change p.2 / (q : ℤ) * (q : ℤ) +
      ((p.2 % (q : ℤ)).toNat : ℤ) = p.2
    rw [h2]
    simpa only [mul_comm, add_comm] using Int.emod_add_mul_ediv p.2 (q : ℤ)

theorem cellIndex_signedCellPoint (q : ℕ) (hq : 0 < q)
    (i j : ℤ) (u v : Fin q) :
    cellIndex q (signedCellPoint q i j u v) = (i, j) := by
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hqpos : (0 : ℤ) < q := by exact_mod_cast hq
  have hu : ((u : ℕ) : ℤ) < (q : ℤ) := by exact_mod_cast u.isLt
  have hv : ((v : ℕ) : ℤ) < (q : ℤ) := by exact_mod_cast v.isLt
  have hfirst := (Int.ediv_emod_unique'' (a := i * (q : ℤ) + (u : ℕ))
    (b := q) (r := (u : ℕ)) (q := i) hq0).2
      ⟨by ring, by exact_mod_cast Nat.zero_le u.val,
        by simp [abs_of_pos hqpos, hu]⟩
  have hsecond := (Int.ediv_emod_unique'' (a := j * (q : ℤ) + (v : ℕ))
    (b := q) (r := (v : ℕ)) (q := j) hq0).2
      ⟨by ring, by exact_mod_cast Nat.zero_le v.val,
        by simp [abs_of_pos hqpos, hv]⟩
  simp [cellIndex, signedCellPoint, hfirst.1, hsecond.1]

/-- An integer square centered at the origin. -/
def latticeBox (R : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(R : ℤ)) R).product (Finset.Icc (-(R : ℤ)) R)

/-- A box that contains the cell indices of `latticeBox R`. -/
def cellIndexBox (q R : ℕ) : Finset (ℤ × ℤ) :=
  let B := R / q + 1
  (Finset.Icc (-(B : ℤ)) B).product (Finset.Icc (-(B : ℤ)) B)

private theorem coordinate_index_bound (q R : ℕ) (hq : 0 < q)
    (x : ℤ) (hx : -(R : ℤ) ≤ x ∧ x ≤ R) :
    -((R / q + 1 : ℕ) : ℤ) ≤ x / (q : ℤ) ∧
      x / (q : ℤ) ≤ (R / q + 1 : ℕ) := by
  have hqpos : (0 : ℤ) < q := by exact_mod_cast hq
  have hR : R ≤ (R / q + 1) * q := by
    calc
      R = R % q + q * (R / q) := (Nat.mod_add_div R q).symm
      _ ≤ q + q * (R / q) := by
        exact Nat.add_le_add_right (Nat.le_of_lt (Nat.mod_lt R hq)) _
      _ = (R / q + 1) * q := by ring
  have hR' : (R : ℤ) ≤ ((R / q + 1 : ℕ) : ℤ) * q := by
    exact_mod_cast hR
  constructor
  · apply (Int.le_ediv_iff_mul_le hqpos).2
    calc
      -((R / q + 1 : ℕ) : ℤ) * (q : ℤ) =
          -(((R / q + 1 : ℕ) : ℤ) * (q : ℤ)) := by ring
      _ ≤ -(R : ℤ) := neg_le_neg hR'
      _ ≤ x := hx.1
  · have hmono := Int.ediv_le_ediv hqpos hx.2
    have hcast : (R : ℤ) / (q : ℤ) = ((R / q : ℕ) : ℤ) := by
      simp
    rw [hcast] at hmono
    omega

theorem cellIndex_mem_cellIndexBox (q R : ℕ) (hq : 0 < q)
    (p : ℤ × ℤ) (hp : p ∈ latticeBox R) :
    cellIndex q p ∈ cellIndexBox q R := by
  have hqpos : (0 : ℤ) < q := by exact_mod_cast hq
  rcases Finset.mem_product.mp hp with ⟨hp1, hp2⟩
  rcases Finset.mem_Icc.mp hp1 with ⟨hlo1, hhi1⟩
  rcases Finset.mem_Icc.mp hp2 with ⟨hlo2, hhi2⟩
  change (p.1 / (q : ℤ), p.2 / (q : ℤ)) ∈
    (Finset.Icc (-(R / q + 1 : ℕ) : ℤ) (R / q + 1)).product
      (Finset.Icc (-(R / q + 1 : ℕ) : ℤ) (R / q + 1))
  apply Finset.mem_product.mpr
  constructor
  · exact Finset.mem_Icc.mpr (coordinate_index_bound q R hq p.1 ⟨hlo1, hhi1⟩)
  · exact Finset.mem_Icc.mpr (coordinate_index_bound q R hq p.2 ⟨hlo2, hhi2⟩)

/-- A finite set's cell indices, used to reindex its sum by cells. -/
def occupiedCells (q : ℕ) (S : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) :=
  S.image (cellIndex q)

/-- The part of `S` occupying a given cell. -/
def cellFiber (q : ℕ) (S : Finset (ℤ × ℤ)) (c : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  S.filter (fun p => cellIndex q p = c)

theorem mem_cellFiber_iff (q : ℕ) (S : Finset (ℤ × ℤ))
    (c p : ℤ × ℤ) : p ∈ cellFiber q S c ↔ p ∈ S ∧ cellIndex q p = c := by
  simp [cellFiber]

/-- Exact finite partition of any lattice set by signed square cells. -/
theorem sum_by_occupied_cells {A : Type*} [AddCommMonoid A]
    (q : ℕ) (S : Finset (ℤ × ℤ)) (f : (ℤ × ℤ) → A) :
    ∑ c ∈ occupiedCells q S, ∑ p ∈ cellFiber q S c, f p = ∑ p ∈ S, f p := by
  classical
  simpa [occupiedCells, cellFiber] using
    (Finset.sum_fiberwise_of_maps_to
      (s := S) (t := S.image (cellIndex q))
      (g := cellIndex q) (f := f)
      (fun p hp => Finset.mem_image_of_mem _ hp))

/-- The offsets in cell `c` whose points belong to `S`. -/
def cellOffsets (q : ℕ) (S : Finset (ℤ × ℤ))
    (c : ℤ × ℤ) : Finset (Fin q × Fin q) :=
  Finset.univ.filter (fun uv => signedCellPoint q c.1 c.2 uv.1 uv.2 ∈ S)

theorem cellOffsets_card_le (q : ℕ) (S : Finset (ℤ × ℤ))
    (c : ℤ × ℤ) : (cellOffsets q S c).card ≤ q ^ 2 := by
  calc
    (cellOffsets q S c).card ≤ (Finset.univ : Finset (Fin q × Fin q)).card :=
      Finset.card_filter_le _ _
    _ = q ^ 2 := by simp [Fintype.card_prod, pow_two]

/-- A partial cell has at least one point in `S` and at least one point
outside `S`. -/
def PartialCell (q : ℕ) (S : Finset (ℤ × ℤ)) (c : ℤ × ℤ) : Prop :=
  (cellOffsets q S c).Nonempty ∧ cellOffsets q S c ≠ Finset.univ

theorem partialCell_inside_outside (q : ℕ) (S : Finset (ℤ × ℤ))
    (c : ℤ × ℤ) (h : PartialCell q S c) :
    ∃ uv vw : Fin q × Fin q,
      signedCellPoint q c.1 c.2 uv.1 uv.2 ∈ S ∧
      signedCellPoint q c.1 c.2 vw.1 vw.2 ∉ S := by
  classical
  obtain ⟨uv, huv⟩ := h.1
  have huvS : signedCellPoint q c.1 c.2 uv.1 uv.2 ∈ S := by
    simpa only [cellOffsets, Finset.mem_filter, Finset.mem_univ, true_and] using huv
  have hout : ∃ vw : Fin q × Fin q, vw ∉ cellOffsets q S c := by
    by_contra hn
    push Not at hn
    apply h.2
    ext vw
    simp [hn vw]
  obtain ⟨vw, hvw⟩ := hout
  refine ⟨uv, vw, huvS, ?_⟩
  simpa only [cellOffsets, Finset.mem_filter, Finset.mem_univ, true_and] using hvw

/-- Reflection sends a signed cell index to its first-quadrant block.
The cell `-1` maps to block `0`, the cell `-2` to block `1`, and so on. -/
def reflectedIndex (i : ℤ) : ℕ :=
  if i < 0 then (-i - 1).toNat else i.toNat

theorem signedCell_natAbs_bounds (q : ℕ) (hq : 0 < q)
    (i : ℤ) (u : Fin q) :
    reflectedIndex i * q ≤ (i * (q : ℤ) + (u : ℕ)).natAbs ∧
      (i * (q : ℤ) + (u : ℕ)).natAbs ≤ (reflectedIndex i + 1) * q := by
  have hqz : (0 : ℤ) < q := by exact_mod_cast hq
  have huz : (0 : ℤ) ≤ (u : ℕ) := by exact_mod_cast Nat.zero_le u.val
  have hult : ((u : ℕ) : ℤ) < (q : ℤ) := by exact_mod_cast u.isLt
  by_cases hi : i < 0
  · have hk : ((reflectedIndex i : ℕ) : ℤ) = -i - 1 := by
      simp [reflectedIndex, hi]
    have hx : i * (q : ℤ) + (u : ℕ) < 0 := by
      nlinarith [mul_nonpos_of_nonpos_of_nonneg
        (show i + 1 ≤ 0 by omega) (le_of_lt hqz)]
    have habs : (((i * (q : ℤ) + (u : ℕ)).natAbs : ℕ) : ℤ) =
        -(i * (q : ℤ) + (u : ℕ)) := by
      rw [Int.natCast_natAbs, abs_of_neg hx]
    constructor <;> apply (Nat.cast_le (α := ℤ)).mp
    · simp only [Nat.cast_mul]
      rw [hk, habs]
      nlinarith

    · simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      rw [hk, habs]
      nlinarith
  · have hk : ((reflectedIndex i : ℕ) : ℤ) = i := by
      simp [reflectedIndex, hi, Int.toNat_of_nonneg (by omega : 0 ≤ i)]
    have hx : 0 ≤ i * (q : ℤ) + (u : ℕ) := by
      nlinarith [mul_nonneg (show 0 ≤ i by omega) (le_of_lt hqz)]
    have habs : (((i * (q : ℤ) + (u : ℕ)).natAbs : ℕ) : ℤ) =
        i * (q : ℤ) + (u : ℕ) := by
      rw [Int.natCast_natAbs, abs_of_nonneg hx]
    constructor <;> apply (Nat.cast_le (α := ℤ)).mp
    · simp only [Nat.cast_mul]
      rw [hk, habs]
      omega
    · simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      rw [hk, habs]
      nlinarith

private theorem natAbs_sq_cast (x : ℤ) :
    (((x.natAbs) ^ 2 : ℕ) : ℤ) = x ^ 2 := by
  simp [sq_abs]

private theorem natAbs_normSq_cast (p : ℤ × ℤ) :
    (((p.1.natAbs ^ 2 + p.2.natAbs ^ 2 : ℕ) : ℤ)) =
      p.1 ^ 2 + p.2 ^ 2 := by
  simp

/-- A partial signed cell meets the first-quadrant boundary path after
reflecting its coordinates.  The mathematical disk is specified by its
membership equivalence, so this applies directly to any finite realization
of the integer norm ball. -/
theorem partialCell_implies_reflected_tileCross
    (X q : ℕ) (hq : 0 < q) (S : Finset (ℤ × ℤ))
    (hS : ∀ p : ℤ × ℤ, p ∈ S ↔ p.1 ^ 2 + p.2 ^ 2 ≤ (X : ℤ))
    (c : ℤ × ℤ) (hc : PartialCell q S c) :
    GaussianBoundary.TileCross
      (fun x y : ℕ => x ^ 2 + y ^ 2 ≤ X) q
      (reflectedIndex c.1) (reflectedIndex c.2) := by
  obtain ⟨uv, vw, huv, hvw⟩ := partialCell_inside_outside q S c hc
  let pin := signedCellPoint q c.1 c.2 uv.1 uv.2
  let pout := signedCellPoint q c.1 c.2 vw.1 vw.2
  have hix := (signedCell_natAbs_bounds q hq c.1 uv.1).1
  have hiy := (signedCell_natAbs_bounds q hq c.2 uv.2).1
  have hox := (signedCell_natAbs_bounds q hq c.1 vw.1).2
  have hoy := (signedCell_natAbs_bounds q hq c.2 vw.2).2
  have hinnat : pin.1.natAbs ^ 2 + pin.2.natAbs ^ 2 ≤ X := by
    have hz := (hS pin).mp huv
    have : (((pin.1.natAbs ^ 2 + pin.2.natAbs ^ 2 : ℕ) : ℤ)) ≤ X := by
      simpa only [natAbs_normSq_cast] using hz
    exact_mod_cast this
  have houtnat : ¬ (pout.1.natAbs ^ 2 + pout.2.natAbs ^ 2 ≤ X) := by
    intro hn
    apply hvw
    apply (hS pout).mpr
    have hz : (((pout.1.natAbs ^ 2 + pout.2.natAbs ^ 2 : ℕ) : ℤ)) ≤ X := by
      exact_mod_cast hn
    simpa only [natAbs_normSq_cast] using hz
  exact GaussianBoundary.tileCross_of_inside_outside
    (GaussianBoundary.disk_downClosed X) hix hiy hox hoy hinnat houtnat

theorem reflectedIndex_lt_of_bounds (i : ℤ) (B : ℕ)
    (hlo : -(B : ℤ) ≤ i) (hhi : i ≤ B) :
    reflectedIndex i < B + 1 := by
  by_cases hi : i < 0
  · simp [reflectedIndex, hi]
    omega
  · simp [reflectedIndex, hi]
    omega

/-- The sign and the reflected index together recover a signed index. -/
def signedIndexCode (i : ℤ) : Bool × ℕ :=
  (decide (i < 0), reflectedIndex i)

theorem signedIndexCode_injective : Function.Injective signedIndexCode := by
  intro a b h
  have hs := congrArg Prod.fst h
  have hr := congrArg Prod.snd h
  by_cases ha : a < 0 <;> by_cases hb : b < 0
  · simp [signedIndexCode, reflectedIndex, ha, hb] at hr
    omega
  · simp [signedIndexCode, ha, hb] at hs
  · simp [signedIndexCode, ha, hb] at hs
  · simp [signedIndexCode, reflectedIndex, ha, hb] at hr
    omega

/-- The cell code records a quadrant and the reflected first-quadrant
cell.  It is injective, even for cells touching an axis. -/
def signedCellCode (c : ℤ × ℤ) : (Bool × Bool) × (ℕ × ℕ) :=
  ((decide (c.1 < 0), decide (c.2 < 0)),
    (reflectedIndex c.1, reflectedIndex c.2))

theorem signedCellCode_injective : Function.Injective signedCellCode := by
  intro c d h
  have hs1 : decide (c.1 < 0) = decide (d.1 < 0) :=
    congrArg (fun x : (Bool × Bool) × (ℕ × ℕ) => x.1.1) h
  have hs2 : decide (c.2 < 0) = decide (d.2 < 0) :=
    congrArg (fun x : (Bool × Bool) × (ℕ × ℕ) => x.1.2) h
  have hr1 : reflectedIndex c.1 = reflectedIndex d.1 :=
    congrArg (fun x : (Bool × Bool) × (ℕ × ℕ) => x.2.1) h
  have hr2 : reflectedIndex c.2 = reflectedIndex d.2 :=
    congrArg (fun x : (Bool × Bool) × (ℕ × ℕ) => x.2.2) h
  apply Prod.ext
  · exact signedIndexCode_injective (Prod.ext hs1 hr1)
  · exact signedIndexCode_injective (Prod.ext hs2 hr2)

/-- The signed cells in the explicit index box which contain both inside
and outside points of `S`. -/
noncomputable def partialCells (q R : ℕ) (S : Finset (ℤ × ℤ)) :
    Finset (ℤ × ℤ) := by
  classical
  exact (cellIndexBox q R).filter (PartialCell q S)

/-- At most `8(R/q+2)` signed cells of the disk are partial.  Four sign
quadrants account for the factor four, and the monotone boundary contributes
at most `2(R/q+2)` first-quadrant cells. -/
theorem disk_partialCells_card_le (X q R : ℕ) (hq : 0 < q)
    (S : Finset (ℤ × ℤ))
    (hS : ∀ p : ℤ × ℤ, p ∈ S ↔ p.1 ^ 2 + p.2 ^ 2 ≤ (X : ℤ)) :
    (partialCells q R S).card ≤ 8 * (R / q + 2) := by
  classical
  let N := R / q + 2
  let T := GaussianBoundary.tileCrossCells
    (fun x y : ℕ => x ^ 2 + y ^ 2 ≤ X) q N
  let C : Finset ((Bool × Bool) × (ℕ × ℕ)) :=
    Finset.univ.product T
  have hinj : (partialCells q R S).card ≤ C.card := by
    apply Finset.card_le_card_of_injOn (f := signedCellCode)
    · intro c hc
      have hc' : c ∈ (cellIndexBox q R).filter (PartialCell q S) := hc
      obtain ⟨hbox, hpartial⟩ := Finset.mem_filter.mp hc'
      apply Finset.mem_product.mpr
      constructor
      · simp
      · change (reflectedIndex c.1, reflectedIndex c.2) ∈ T
        unfold T GaussianBoundary.tileCrossCells
        apply Finset.mem_filter.mpr
        constructor
        · apply Finset.mem_product.mpr
          rcases Finset.mem_product.mp hbox with ⟨h1, h2⟩
          rcases Finset.mem_Icc.mp h1 with ⟨hlo1, hhi1⟩
          rcases Finset.mem_Icc.mp h2 with ⟨hlo2, hhi2⟩
          constructor <;> apply Finset.mem_range.mpr
          · exact reflectedIndex_lt_of_bounds c.1 (R / q + 1)
              hlo1 hhi1
          · exact reflectedIndex_lt_of_bounds c.2 (R / q + 1)
              hlo2 hhi2
        · exact partialCell_implies_reflected_tileCross X q hq S hS c hpartial
    · intro c _ d _ heq
      exact signedCellCode_injective heq
  have hT : T.card ≤ 2 * N := GaussianBoundary.disk_boundary_tile_count_le X q N
  calc
    (partialCells q R S).card ≤ C.card := hinj
    _ = 4 * T.card := by simp [C, Finset.card_product]
    _ ≤ 4 * (2 * N) := Nat.mul_le_mul_left 4 hT
    _ = 8 * (R / q + 2) := by dsimp [N]; omega

theorem signedCellPoint_injective (q : ℕ) (i j : ℤ) :
    Function.Injective (fun uv : Fin q × Fin q =>
      signedCellPoint q i j uv.1 uv.2) := by
  intro uv vw h
  have hfirst := congrArg Prod.fst h
  have hsecond := congrArg Prod.snd h
  have huval : uv.1.val = vw.1.val := by
    change i * (q : ℤ) + (uv.1.val : ℤ) =
      i * (q : ℤ) + (vw.1.val : ℤ) at hfirst
    omega
  have hvval : uv.2.val = vw.2.val := by
    change j * (q : ℤ) + (uv.2.val : ℤ) =
      j * (q : ℤ) + (vw.2.val : ℤ) at hsecond
    omega
  exact Prod.ext (Fin.ext huval) (Fin.ext hvval)

theorem cellOffset_signedCellPoint (q : ℕ) (hq : 0 < q)
    (i j : ℤ) (u v : Fin q) :
    cellOffset q hq (signedCellPoint q i j u v) = (u, v) := by
  have hrec := signedCellPoint_cellIndex_cellOffset q hq
    (signedCellPoint q i j u v)
  rw [cellIndex_signedCellPoint q hq i j u v] at hrec
  exact signedCellPoint_injective q i j hrec

theorem cellFiber_eq_image_offsets (q : ℕ) (hq : 0 < q)
    (S : Finset (ℤ × ℤ)) (c : ℤ × ℤ) :
    cellFiber q S c =
      (cellOffsets q S c).image
        (fun uv => signedCellPoint q c.1 c.2 uv.1 uv.2) := by
  ext p
  constructor
  · intro hp
    obtain ⟨hpS, hindex⟩ := (mem_cellFiber_iff q S c p).mp hp
    have hrec := signedCellPoint_cellIndex_cellOffset q hq p
    rw [hindex] at hrec
    apply Finset.mem_image.mpr
    refine ⟨cellOffset q hq p, ?_, hrec⟩
    simpa [cellOffsets, hrec] using hpS
  · intro hp
    obtain ⟨uv, huv, rfl⟩ := Finset.mem_image.mp hp
    apply (mem_cellFiber_iff q S c _).mpr
    have huvS : signedCellPoint q c.1 c.2 uv.1 uv.2 ∈ S := by
      simpa only [cellOffsets, Finset.mem_filter, Finset.mem_univ, true_and] using huv
    exact ⟨huvS,
      cellIndex_signedCellPoint q hq c.1 c.2 uv.1 uv.2⟩

/-- Each cell fiber is an exact sum over its unique `Fin q × Fin q`
offsets. -/
theorem sum_cellFiber_offsets {A : Type*} [AddCommMonoid A]
    (q : ℕ) (hq : 0 < q) (S : Finset (ℤ × ℤ))
    (c : ℤ × ℤ) (f : (ℤ × ℤ) → A) :
    ∑ p ∈ cellFiber q S c, f p =
      ∑ uv ∈ cellOffsets q S c,
        f (signedCellPoint q c.1 c.2 uv.1 uv.2) := by
  rw [cellFiber_eq_image_offsets q hq S c]
  exact Finset.sum_image (fun uv _ vw _ h => signedCellPoint_injective q c.1 c.2 h)

/-- Exact lattice sum as a finite sum of complete or partial signed
`q × q` cells. -/
theorem sum_by_cell_offsets {A : Type*} [AddCommMonoid A]
    (q : ℕ) (hq : 0 < q) (S : Finset (ℤ × ℤ))
    (f : (ℤ × ℤ) → A) :
    ∑ c ∈ occupiedCells q S,
      ∑ uv ∈ cellOffsets q S c,
        f (signedCellPoint q c.1 c.2 uv.1 uv.2) =
          ∑ p ∈ S, f p := by
  simp_rw [← sum_cellFiber_offsets q hq S]
  exact sum_by_occupied_cells q S f

theorem occupiedCells_subset_cellIndexBox (q R : ℕ) (hq : 0 < q)
    (S : Finset (ℤ × ℤ)) (hS : S ⊆ latticeBox R) :
    occupiedCells q S ⊆ cellIndexBox q R := by
  intro c hc
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hc
  exact cellIndex_mem_cellIndexBox q R hq p (hS hp)

theorem cellOffsets_eq_empty_of_not_occupied (q : ℕ) (hq : 0 < q)
    (S : Finset (ℤ × ℤ)) (c : ℤ × ℤ)
    (hc : c ∉ occupiedCells q S) : cellOffsets q S c = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro uv huv
  have hp : signedCellPoint q c.1 c.2 uv.1 uv.2 ∈ S := by
    simpa only [cellOffsets, Finset.mem_filter, Finset.mem_univ, true_and] using huv
  apply hc
  apply Finset.mem_image.mpr
  exact ⟨signedCellPoint q c.1 c.2 uv.1 uv.2, hp,
    cellIndex_signedCellPoint q hq c.1 c.2 uv.1 uv.2⟩

/-- A finite lattice set in the box of radius `R` can be summed over the
explicit box of indices of radius `R / q + 1`.  Unoccupied cells contribute
zero. -/
theorem sum_by_cellIndexBox {A : Type*} [AddCommMonoid A]
    (q R : ℕ) (hq : 0 < q) (S : Finset (ℤ × ℤ))
    (hS : S ⊆ latticeBox R) (f : (ℤ × ℤ) → A) :
    ∑ c ∈ cellIndexBox q R,
      ∑ uv ∈ cellOffsets q S c,
        f (signedCellPoint q c.1 c.2 uv.1 uv.2) =
          ∑ p ∈ S, f p := by
  have hsubset := occupiedCells_subset_cellIndexBox q R hq S hS
  calc
    ∑ c ∈ cellIndexBox q R,
        ∑ uv ∈ cellOffsets q S c,
          f (signedCellPoint q c.1 c.2 uv.1 uv.2) =
        ∑ c ∈ occupiedCells q S,
          ∑ uv ∈ cellOffsets q S c,
            f (signedCellPoint q c.1 c.2 uv.1 uv.2) := by
              symm
              apply Finset.sum_subset hsubset
              intro c _ hc
              simp [cellOffsets_eq_empty_of_not_occupied q hq S c hc]
    _ = ∑ p ∈ S, f p := sum_by_cell_offsets q hq S f

end Erdos940.Quartic.GaussianCellPartition
