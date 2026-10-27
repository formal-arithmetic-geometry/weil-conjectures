/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q46
-/
module

public import Sheaf.RingTheory.RestrictedSeriesPresentation
public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Adjoining polynomial variables to restricted series

Source: Bosch, Lectures on Formal and Rigid Geometry (April 2008), Section 1.2,
Theorem 8 and Proposition 14 proof, printed pp. 12--13 and 15--16
(blueprint: def-trf-restricted-series-coefficient-extension).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u

namespace RestrictedSeries

/-- Renaming the first `r` variables into `r + s` variables preserves coefficient decay.
Source: Bosch, Section 1.2, coefficient description of Tate algebras, printed pp. 8--9
(blueprint: def-trf-restricted-series-coefficient-extension).

Proof: `Fin.castAdd s` embeds the old variables as the first coordinates. The induced
embedding of exponent vectors preserves each old coefficient and gives zero elsewhere,
by `MvPowerSeries.coeff_embDomain_rename` and `MvPowerSeries.coeff_rename_eq_zero`.
For every positive epsilon, the new coefficients of norm at least epsilon are therefore
the image of the finite set of such old coefficients. This is precisely restrictedness.
-/
theorem coefficientExtension_restricted
    (K : Type u) [NormedField K] [IsUltrametricDist K] (r s : ℕ)
    (a : MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin r ↦ (1 : ℝ))) :
    MvPowerSeries.IsRestricted (fun _ : Fin (r + s) ↦ (1 : ℝ))
      (MvPowerSeries.rename (Fin.castAdd s) a.val) := by
  sorry

/-- The canonical coefficient inclusion, retaining the first `r` variables.
Source: Bosch, Section 1.2, Theorem 8, printed pp. 12--13
(blueprint: def-trf-restricted-series-coefficient-extension). -/
noncomputable def coefficientExtension
    (K : Type u) [NormedField K] [IsUltrametricDist K] (r s : ℕ) :
    (MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin r ↦ (1 : ℝ))) →+*
      (MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin (r + s) ↦ (1 : ℝ))) :=
  ((MvPowerSeries.rename (R := K) (Fin.castAdd s)).toRingHom.comp
    (MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin r ↦ (1 : ℝ))).subtype).codRestrict
      _ (coefficientExtension_restricted K r s)

/-- The larger Tate algebra as an algebra over its first `r` variables.
Source: Bosch, Section 1.2, Theorem 8, printed pp. 12--13
(blueprint: def-trf-restricted-series-coefficient-extension). -/
noncomputable instance coefficientExtensionAlgebra
    (K : Type u) [NormedField K] [IsUltrametricDist K] (r s : ℕ) :
    Algebra
      (MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin r ↦ (1 : ℝ)))
      (MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin (r + s) ↦ (1 : ℝ))) :=
  (coefficientExtension K r s).toAlgebra

/-- The canonical inclusion of polynomials in the last `s` variables, with restricted
series coefficients in the first `r` variables. Source: Bosch, Section 1.2,
Proposition 14 proof, printed pp. 15--16
(blueprint: def-trf-restricted-series-coefficient-extension). -/
noncomputable def coefficientPolynomialInclusion
    (K : Type u) [NormedField K] [IsUltrametricDist K] (r s : ℕ) :
    MvPolynomial (Fin s)
      (MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin r ↦ (1 : ℝ))) →ₐ[
        MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin r ↦ (1 : ℝ))]
      (MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin (r + s) ↦ (1 : ℝ))) :=
  MvPolynomial.aeval (fun i : Fin s ↦
    ⟨MvPowerSeries.X (Fin.natAdd r i), MvPowerSeries.isRestricted_monomial _ _ _⟩)

/-- The canonical quotient map induced by the coefficient-polynomial inclusion.
The target ideal is exactly the extension of the given polynomial ideal.
Source: Bosch, Section 1.2, Proposition 14 proof, printed pp. 15--16
(blueprint: def-trf-restricted-series-coefficient-extension). -/
noncomputable def coefficientPolynomialQuotientMap
    (K : Type u) [NormedField K] [IsUltrametricDist K] (r s : ℕ)
    (J : Ideal (MvPolynomial (Fin s)
      (MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin r ↦ (1 : ℝ))))) :
    (MvPolynomial (Fin s)
      (MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin r ↦ (1 : ℝ))) ⧸ J) →ₐ[
        MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin r ↦ (1 : ℝ))]
      ((MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin (r + s) ↦ (1 : ℝ))) ⧸
        J.map (coefficientPolynomialInclusion K r s).toRingHom) :=
  Ideal.quotientMapₐ _ (coefficientPolynomialInclusion K r s) Ideal.le_comap_map

end RestrictedSeries
