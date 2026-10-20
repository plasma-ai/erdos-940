import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Boundary cells of a monotone lattice region

A disk in one quadrant is downward closed in each coordinate.  A square
cell intersecting its boundary has its lower-left corner in the disk and a
point below its upper-right corner outside.  The latter cells are bounded
by a monotone boundary path: at most one vertical crossing per column and
at most one horizontal crossing per row.  This purely combinatorial bound
is the boundary-cell input for the Gaussian disk Riemann-sum estimate.
-/

namespace Erdos940.Quartic.GaussianBoundary

open Finset

def DownClosed (S : ℕ → ℕ → Prop) : Prop :=
  ∀ ⦃x y x' y'⦄, x' ≤ x → y' ≤ y → S x y → S x' y'

def TileCross (S : ℕ → ℕ → Prop) (q i j : ℕ) : Prop :=
  S (i * q) (j * q) ∧ ¬ S ((i + 1) * q) ((j + 1) * q)

/-- Any square containing both an inside and an outside lattice point is
counted by `TileCross`. -/
theorem tileCross_of_inside_outside {S : ℕ → ℕ → Prop} (hS : DownClosed S)
    {q i j x y x' y' : ℕ}
    (hix : i * q ≤ x) (hiy : j * q ≤ y)
    (hox : x' ≤ (i + 1) * q) (hoy : y' ≤ (j + 1) * q)
    (hin : S x y) (hout : ¬ S x' y') : TileCross S q i j := by
  constructor
  · exact hS hix hiy hin
  · intro hupp
    exact hout (hS hox hoy hupp)

private def VerticalCross (S : ℕ → ℕ → Prop) (q i j : ℕ) : Prop :=
  S (i * q) (j * q) ∧ ¬ S (i * q) ((j + 1) * q)

private def HorizontalCross (S : ℕ → ℕ → Prop) (q i j : ℕ) : Prop :=
  S (i * q) ((j + 1) * q) ∧ ¬ S ((i + 1) * q) ((j + 1) * q)

private theorem tileCross_vertical_or_horizontal {S : ℕ → ℕ → Prop}
    {q i j : ℕ} (h : TileCross S q i j) :
    VerticalCross S q i j ∨ HorizontalCross S q i j := by
  rcases h with ⟨hlow, hupp⟩
  by_cases hmid : S (i * q) ((j + 1) * q)
  · exact Or.inr ⟨hmid, hupp⟩
  · exact Or.inl ⟨hlow, hmid⟩

private theorem vertical_unique {S : ℕ → ℕ → Prop} (hS : DownClosed S)
    {q i j k : ℕ} (hj : VerticalCross S q i j)
    (hk : VerticalCross S q i k) : j = k := by
  rcases lt_trichotomy j k with hlt | heq | hgt
  · exfalso
    exact hj.2 (hS (le_refl _) (Nat.mul_le_mul_right q (by omega)) hk.1)
  · exact heq
  · exfalso
    exact hk.2 (hS (le_refl _) (Nat.mul_le_mul_right q (by omega)) hj.1)

private theorem horizontal_unique {S : ℕ → ℕ → Prop} (hS : DownClosed S)
    {q i k j : ℕ} (hi : HorizontalCross S q i j)
    (hk : HorizontalCross S q k j) : i = k := by
  rcases lt_trichotomy i k with hlt | heq | hgt
  · exfalso
    exact hi.2 (hS (Nat.mul_le_mul_right q (by omega)) (le_refl _) hk.1)
  · exact heq
  · exfalso
    exact hk.2 (hS (Nat.mul_le_mul_right q (by omega)) (le_refl _) hi.1)

noncomputable def tileCrossCells (S : ℕ → ℕ → Prop) (q N : ℕ) :
    Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.range N).product (Finset.range N)).filter
    fun p => TileCross S q p.1 p.2

/-- In an `N × N` array of square cells, at most `2N` cells cross the
boundary of any downward-closed region.  The upper-right test may include
some cells that merely touch the boundary, which only strengthens the
usefulness of this upper bound. -/
theorem card_tileCross_le_two_mul (S : ℕ → ℕ → Prop) (hS : DownClosed S)
    (q N : ℕ) :
    (tileCrossCells S q N).card ≤ 2 * N := by
  classical
  unfold tileCrossCells
  let rect : Finset (ℕ × ℕ) := (Finset.range N).product (Finset.range N)
  let V : Finset (ℕ × ℕ) := rect.filter fun p => VerticalCross S q p.1 p.2
  let H : Finset (ℕ × ℕ) := rect.filter fun p => HorizontalCross S q p.1 p.2
  have hcover : (rect.filter fun p => TileCross S q p.1 p.2) ⊆ V ∪ H := by
    intro p hp
    obtain ⟨hrect, hcross⟩ := Finset.mem_filter.mp hp
    rcases tileCross_vertical_or_horizontal hcross with hv | hh
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hrect, hv⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hrect, hh⟩))
  have hV : V.card ≤ N := by
    calc
      V.card ≤ (Finset.range N).card := by
        apply Finset.card_le_card_of_injOn (f := Prod.fst)
        · intro p hp
          exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
        · intro p hp p' hp' heq
          apply Prod.ext heq
          have hk := (Finset.mem_filter.mp hp').2
          rw [← heq] at hk
          exact vertical_unique hS (Finset.mem_filter.mp hp).2 hk
      _ = N := Finset.card_range N
  have hH : H.card ≤ N := by
    calc
      H.card ≤ (Finset.range N).card := by
        apply Finset.card_le_card_of_injOn (f := Prod.snd)
        · intro p hp
          exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2
        · intro p hp p' hp' heq
          apply Prod.ext
          · have hk := (Finset.mem_filter.mp hp').2
            rw [← heq] at hk
            exact horizontal_unique hS (Finset.mem_filter.mp hp).2 hk
          · exact heq
      _ = N := Finset.card_range N
  calc
    (rect.filter fun p => TileCross S q p.1 p.2).card ≤ (V ∪ H).card :=
      Finset.card_le_card hcover
    _ ≤ V.card + H.card := Finset.card_union_le _ _
    _ ≤ 2 * N := by omega

/-- A first-quadrant disk is downward closed. -/
theorem disk_downClosed (X : ℕ) :
    DownClosed (fun x y : ℕ => x ^ 2 + y ^ 2 ≤ X) := by
  intro x y x' y' hx hy hxy
  have hxx : x' ^ 2 ≤ x ^ 2 := by gcongr
  have hyy : y' ^ 2 ≤ y ^ 2 := by gcongr
  omega

/-- At most `2N` cells of an `N × N` first-quadrant grid cross the disk
boundary, for any cell side length `q`. -/
theorem disk_boundary_tile_count_le (X q N : ℕ) :
    (tileCrossCells (fun x y : ℕ => x ^ 2 + y ^ 2 ≤ X) q N).card ≤ 2 * N :=
  card_tileCross_le_two_mul _ (disk_downClosed X) q N

/-- Summing a radial weight over the first-quadrant square lattice, grouped
by its `ℓ∞` radius. -/
def squareMaxSum (w : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, w (max i j)

theorem squareMaxSum_succ (w : ℕ → ℝ) (N : ℕ) :
    squareMaxSum w (N + 1) = squareMaxSum w N + (2 * N + 1) * w N := by
  have hrow (i : ℕ) (hi : i ∈ Finset.range N) : max i N = N :=
    max_eq_right (Nat.le_of_lt (Finset.mem_range.mp hi))
  have hcol (j : ℕ) (hj : j ∈ Finset.range N) : max N j = N :=
    max_eq_left (Nat.le_of_lt (Finset.mem_range.mp hj))
  unfold squareMaxSum
  rw [Finset.sum_range_succ]
  simp_rw [Finset.sum_range_succ]
  have hr : (∑ i ∈ Finset.range N, w (max i N)) = N * w N := by
    calc
      (∑ i ∈ Finset.range N, w (max i N)) =
          ∑ _i ∈ Finset.range N, w N :=
        Finset.sum_congr rfl (fun i hi => by rw [hrow i hi])
      _ = N * w N := by simp
  have hc : (∑ j ∈ Finset.range N, w (max N j)) = N * w N := by
    calc
      (∑ j ∈ Finset.range N, w (max N j)) =
          ∑ _j ∈ Finset.range N, w N :=
        Finset.sum_congr rfl (fun j hj => by rw [hcol j hj])
      _ = N * w N := by simp
  rw [Finset.sum_add_distrib, hr, hc, max_self]
  ring

/-- The total reciprocal `ℓ∞` radius of the cells in an `N × N` grid is
linear in `N`.  This is the summation needed after applying the angular
Lipschitz bound to complete cells. -/
theorem square_reciprocal_max_sum_le (N : ℕ) :
    squareMaxSum (fun k => if k = 0 then 0 else (k : ℝ)⁻¹) N ≤ 3 * N := by
  let w : ℕ → ℝ := fun k => if k = 0 then 0 else (k : ℝ)⁻¹
  change squareMaxSum w N ≤ 3 * N
  induction N with
  | zero => simp [squareMaxSum]
  | succ N ih =>
      rw [squareMaxSum_succ]
      by_cases hN : N = 0
      · subst N
        simp [w, squareMaxSum]
      have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
      have hNge : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN
      have hw : (2 * (N : ℝ) + 1) * w N ≤ 3 := by
        simp only [w, ite_eq_right hN]
        rw [← div_eq_mul_inv]
        apply (div_le_iff₀ hNpos).2
        linarith
      calc
        squareMaxSum w N + (2 * (N : ℝ) + 1) * w N ≤
            3 * N + 3 := add_le_add ih hw
        _ = 3 * (N + 1 : ℕ) := by push_cast; ring

end Erdos940.Quartic.GaussianBoundary
