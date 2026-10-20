import Erdos940.Quartic.QuarticTraceEleven
import Erdos940.Quartic.BaseTraceIntrinsic

/-!
# Normalizing a quartic Gauss trace

The complex 21-term point-count identity has a real local-density form.
This is a purely algebraic bridge; the Gauss-sum and character evaluations
are supplied separately.
-/

namespace Erdos940.Quartic

/-- Convert the normalized complex point-count trace into the real
prime-field density used by the local sieve. -/
theorem quartic_complex_trace_to_real_density
    (q N : ℕ) (hq : 1 < q) (z : ℂ)
    (htrace : (q : ℂ) * (N : ℂ) =
      (q : ℂ) ^ 4 + ((q - 1 : ℕ) : ℂ) * (q : ℂ) ^ 2 * z) :
    (N : ℝ) / (q : ℝ) ^ 3 =
      1 + z.re * ((q : ℝ)⁻¹ - ((q : ℝ) ^ 2)⁻¹) := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hqsub : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ q)]
    norm_num
  have hcast : ((q - 1 : ℕ) : ℂ) * (q : ℂ) ^ 2 =
      ((((q - 1 : ℕ) : ℝ) * (q : ℝ) ^ 2 : ℝ) : ℂ) := by
    norm_cast
  rw [hcast] at htrace
  have hre := congrArg Complex.re htrace
  simp only [Complex.add_re, Complex.mul_re] at hre
  simp only [← Complex.ofReal_natCast, ← Complex.ofReal_pow,
    Complex.ofReal_re, Complex.ofReal_im] at hre
  rw [hqsub] at hre
  field_simp
  nlinarith [hre]

/-- The quartic Gauss trace, normalized term by term, is exactly the
real trace coefficient in the prime-field local density. -/
theorem quartic_gauss_trace_local_density
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 4) (ψ : AddChar (ZMod q) ℂ)
    (hψ : ψ.IsPrimitive) (a : Fin 4 → ZMod q)
    (ha : ∀ i, a i ≠ 0) :
    (Nat.card {x : Fin 4 → ZMod q // ∑ i, a i * x i ^ 4 = 0} : ℝ) /
        (q : ℝ) ^ 3 =
      1 + (∑ j ∈ quarticExponents, quarticGaussTerm q χ ψ a j).re *
        ((q : ℝ)⁻¹ - ((q : ℝ) ^ 2)⁻¹) := by
  let N := Nat.card {x : Fin 4 → ZMod q // ∑ i, a i * x i ^ 4 = 0}
  have hq : (q : ℂ) ≠ 0 := by
    exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hsum :
      (∑ j ∈ quarticExponents,
          ∏ i : Fin 4,
            (χ ^ (j i : ℕ))⁻¹ (a i) *
              gaussSum (χ ^ (j i : ℕ)) ψ) =
        (q : ℂ) ^ 2 *
          ∑ j ∈ quarticExponents, quarticGaussTerm q χ ψ a j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [quarticGaussTerm]
    field_simp
  have htrace := quartic_zero_count_gauss_trace_q_sub_one
    q χ hχ ψ hψ a ha
  rw [hsum] at htrace
  have htrace' : (q : ℂ) * (N : ℂ) =
      (q : ℂ) ^ 4 + ((q - 1 : ℕ) : ℂ) * (q : ℂ) ^ 2 *
        ∑ j ∈ quarticExponents, quarticGaussTerm q χ ψ a j := by
    simpa only [N, mul_assoc] using htrace
  exact quartic_complex_trace_to_real_density q N
    (Fact.out : q.Prime).one_lt
    (∑ j ∈ quarticExponents, quarticGaussTerm q χ ψ a j) htrace'

/-- The trace coefficient in the real local formula is bounded by 21. -/
theorem quartic_gauss_trace_real_abs_le_21
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 4) (ψ : AddChar (ZMod q) ℂ)
    (hψ : ψ.IsPrimitive) (a : Fin 4 → ZMod q)
    (ha : ∀ i, a i ≠ 0) :
    |(∑ j ∈ quarticExponents, quarticGaussTerm q χ ψ a j).re| ≤ 21 :=
  (Complex.abs_re_le_norm _).trans
    (quarticGaussTrace_norm_le_21 q χ hχ ψ hψ a ha)

/-- For a split-prime quartic character, the real Gauss trace equals
the intrinsic coefficient defined directly from the zero count. -/
theorem quarticIntrinsicTrace_eq_gauss_trace
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 4) (ψ : AddChar (ZMod q) ℂ)
    (hψ : ψ.IsPrimitive) (a : Fin 4 → ZMod q)
    (ha : ∀ i, a i ≠ 0) :
    quarticIntrinsicTrace q a =
      (∑ j ∈ quarticExponents, quarticGaussTerm q χ ψ a j).re := by
  letI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  exact quarticIntrinsicTrace_eq_of_local_density q
    (Fact.out : q.Prime).one_lt a _
    (quartic_gauss_trace_local_density q χ hχ ψ hψ a ha)

theorem quarticIntrinsicTrace_abs_le_21_of_quartic_character
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 4) (ψ : AddChar (ZMod q) ℂ)
    (hψ : ψ.IsPrimitive) (a : Fin 4 → ZMod q)
    (ha : ∀ i, a i ≠ 0) :
    |quarticIntrinsicTrace q a| ≤ 21 := by
  rw [quarticIntrinsicTrace_eq_gauss_trace q χ hχ ψ hψ a ha]
  exact quartic_gauss_trace_real_abs_le_21 q χ hχ ψ hψ a ha

/-- The intrinsic split-prime trace is the sum of the eleven real
character constituents once the Gaussian Jacobi generator is chosen. -/
theorem quarticIntrinsicTrace_eq_eleven_real_characters
    (q : ℕ) [Fact q.Prime] (χ : MulChar (ZMod q) ℂ)
    (hχ : orderOf χ = 4) (ψ : AddChar (ZMod q) ℂ)
    (hψ : ψ.IsPrimitive) (a : Fin 4 → ZMod q)
    (ha : ∀ i, a i ≠ 0)
    (π : GaussianInt) (hJ : jacobiSum χ χ ^ 2 = (π : ℂ) ^ 2) :
    quarticIntrinsicTrace q a =
      ∑ k : Fin 11, (quarticElevenCharacterConstituent q χ a π k).re := by
  rw [quarticIntrinsicTrace_eq_gauss_trace q χ hχ ψ hψ a ha,
    quarticGaussTrace_eq_eleven_characters q χ hχ ψ hψ a π hJ]
  simp only [Complex.re_sum]

end Erdos940.Quartic
