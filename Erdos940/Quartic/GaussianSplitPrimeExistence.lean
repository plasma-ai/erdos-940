import Mathlib.NumberTheory.SumTwoSquares

/-!
# A normalized Gaussian prime above every split rational prime

Fermat's two-squares theorem gives a Gaussian integer of norm q. Since
q is odd, exactly one coordinate is odd; we choose it as the real part.
-/

namespace Erdos940.Quartic

/-- Every prime congruent to one modulo four is the norm of a Gaussian
integer with odd real and even imaginary parts. -/
theorem exists_normalized_gaussian_prime
    (q : ℕ) [Fact q.Prime] (hqmod : q % 4 = 1) :
    ∃ π : GaussianInt,
      π.norm = q ∧
      (π.re : ZMod 2) = 1 ∧
      (π.im : ZMod 2) = 0 := by
  obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq (by omega : q % 4 ≠ 3)
  have hqodd : q % 2 = 1 := by omega
  have hsqa : a ^ 2 % 2 = a % 2 := by
    have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
    rcases ha with ha | ha <;> simp [Nat.pow_mod, ha]
  have hsqb : b ^ 2 % 2 = b % 2 := by
    have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
    rcases hb with hb | hb <;> simp [Nat.pow_mod, hb]
  have hparity :
      (a % 2 = 1 ∧ b % 2 = 0) ∨
        (a % 2 = 0 ∧ b % 2 = 1) := by
    have h := congrArg (fun n : ℕ => n % 2) hab
    omega
  rcases hparity with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · refine ⟨⟨a, b⟩, ?_, ?_, ?_⟩
    · simpa [Zsqrtd.norm, pow_two] using congrArg (fun n : ℕ => (n : ℤ)) hab
    · simpa using congrArg (fun n : ℕ => (n : ZMod 2)) ha
    · simpa using congrArg (fun n : ℕ => (n : ZMod 2)) hb
  · refine ⟨⟨b, a⟩, ?_, ?_, ?_⟩
    · have hswap : b ^ 2 + a ^ 2 = q := by omega
      simpa [Zsqrtd.norm, pow_two] using congrArg (fun n : ℕ => (n : ℤ)) hswap
    · simpa using congrArg (fun n : ℕ => (n : ZMod 2)) hb
    · simpa using congrArg (fun n : ℕ => (n : ZMod 2)) ha

end Erdos940.Quartic
