import Erdos940.Quartic.GaussianIdealEulerIdentity

/-!
# Finite Gaussian prime Euler products

For a fixed finite set of Gaussian prime ideals, simultaneous truncation
of their local geometric series converges to the finite Euler product.
-/

namespace Erdos940.Quartic.GaussianFiniteEulerLimit

open scoped NumberField
open scoped Topology
open NumberField IsDedekindDomain
open Filter
open Erdos940.Quartic
open Erdos940.Quartic.GaussianIdealEulerIdentity

theorem weightedIdeal_finitePrime_truncatedProduct_tendsto
    (w : Ideal (𝓞 GaussianField) → ℂ)
    (hw : ∀ I, ‖w I‖ ≤ 1)
    (hwone : w ⊤ = 1)
    (hwmul : ∀ I J, w (I * J) = w I * w J)
    (σ : ℝ) (hσ : 1 < σ)
    (S : Finset (HeightOneSpectrum (𝓞 GaussianField))) :
    Tendsto
      (fun N : ℕ => ∏ P ∈ S,
        ∑ e ∈ Finset.range N, weightedIdealTerm w (σ : ℂ) (P.asIdeal ^ e))
      atTop
      (𝓝 (∏ P ∈ S,
        (1 - weightedIdealTerm w (σ : ℂ) P.asIdeal)⁻¹)) := by
  have hlocal (P : HeightOneSpectrum (𝓞 GaussianField)) :
      Tendsto
        (fun N : ℕ =>
          ∑ e ∈ Finset.range N,
            weightedIdealTerm w (σ : ℂ) (P.asIdeal ^ e))
        atTop
        (𝓝 ((1 - weightedIdealTerm w (σ : ℂ) P.asIdeal)⁻¹)) := by
    rw [weightedIdeal_local_geometric_series w hw hwone hwmul σ hσ P]
    simpa only [weightedIdealTerm_pow w _ hwone hwmul] using
      (summable_geometric_of_norm_lt_one
        (norm_weightedIdealTerm_prime_lt_one w hw σ hσ P)).hasSum.tendsto_sum_nat
  exact tendsto_finsetProd S (fun P _ => hlocal P)

end Erdos940.Quartic.GaussianFiniteEulerLimit
