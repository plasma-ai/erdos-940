import Erdos940.Quartic.GaussianIdealEulerProduct
import Erdos940.Quartic.GaussianIdealEulerIdentity

/-!
# Aligning the smoothed Gaussian prime term with the ideal Dirichlet term
-/

namespace Erdos940.Quartic.GaussianIdealEulerAlignment

open scoped NumberField
open NumberField IsDedekindDomain
open Erdos940.Quartic.GaussianIdealEulerProduct
open Erdos940.Quartic.GaussianIdealEulerIdentity
open Erdos940.Quartic.GaussianIdealLatticeSeries

/-- The prime term in the Euler logarithm is precisely the prime ideal
term of the norm-indexed Dirichlet series at the smoothed exponent. -/
theorem quarticPrimeTerm_eq_idealTerm
    (R : 𝓞 GaussianField) (ι : GaussianField →+* ℂ)
    (B : ℝ)
    (P : HeightOneSpectrum (𝓞 GaussianField)) :
    quarticPrimeTerm R ι B P =
      idealTerm R ι ((1 + 1 / Real.log B : ℝ) : ℂ) P.asIdeal := by
  rw [quarticPrimeTerm_eq_weight_div_cpow, idealTerm, if_neg P.ne_bot]

end Erdos940.Quartic.GaussianIdealEulerAlignment
