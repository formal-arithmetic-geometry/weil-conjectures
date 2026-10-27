/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q78
-/
module

public import Sheaf.RingTheory.RestrictedSeriesPresentation
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Units of a Tate algebra

Source: Bosch, Lectures on Formal and Rigid Geometry (2008), Section 1.2,
Corollary 4, printed p. 10 (blueprint: lem-trf-tate-unit-coefficient-criterion).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

universe u

namespace RestrictedSeries

/-- A restricted series is invertible precisely when its constant coefficient strictly
exceeds the Gauss norm of its nonconstant tail. The constant is then nonzero.
With no variables every series is constant and its tail has Gauss norm zero.
Source: Bosch, Lectures on Formal and Rigid Geometry (2008), Section 1.2,
Corollary 4, printed p. 10 (blueprint: lem-trf-tate-unit-coefficient-criterion).

Proof:
1. By lem-trf-restricted-series-gauss-completion the Gauss norm is complete and
   submultiplicative. A nonzero restricted coefficient family attains its norm:
   choose a coefficient of norm b > 0, maximize over the finite nonempty set of
   coefficients of norm at least b/2, and compare with the remaining coefficients.
   This also applies to the tail. Scalar multiplication scales the norm by the
   scalar's absolute value, including for the zero scalar.
2. If fg = 1, choose a coefficient a of f attaining its norm. Normalize F = a⁻¹f
   and G = ag. By lem-trf-tate-gauss-multiplicative both have norm one and FG = 1.
   Apply lem-trf-tate-unit-ball-polynomial-reduction to obtain inverse polynomials
   over the residue field. By lem-trf-mvpolynomial-divisor-nonzero-constant the
   reduction of F is a nonzero constant.
3. The reduction's coefficient formula gives norm one for the constant of F and
   norm strictly less than one for every nonconstant coefficient. Norm attainment
   for the restricted tail makes its supremum strictly less than one, also when
   the tail is zero. Scaling back gives the stated strict inequality.
4. Conversely, the strict inequality implies c₀ ≠ 0. Set h = 1 - c₀⁻¹f; its Gauss
   norm is less than one. Completeness and lem-trf-complete-normed-ring-geometric-inverse
   give S = ∑ hⁿ with (1-h)S = S(1-h) = 1. Then c₀⁻¹S is an inverse of f.
   For r = 0 the only multi-index is zero, so f is its constant series and the
   tail is zero. The criterion reduces to nonvanishing in the field, and f = 0
   satisfies neither side. -/
theorem tate_unit_coefficient_criterion
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (r : ℕ)
    (f : MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin r ↦ (1 : ℝ))) :
    (IsUnit f ↔
      MvPowerSeries.gaussNorm (norm : K → ℝ) (fun _ : Fin r ↦ 1)
        (f - constants K r (MvPowerSeries.constantCoeff f.val)).val <
          ‖MvPowerSeries.constantCoeff f.val‖) ∧
    ((MvPowerSeries.gaussNorm (norm : K → ℝ) (fun _ : Fin r ↦ 1)
        (f - constants K r (MvPowerSeries.constantCoeff f.val)).val <
          ‖MvPowerSeries.constantCoeff f.val‖) →
      MvPowerSeries.constantCoeff f.val ≠ 0) ∧
    (r = 0 →
      f = constants K r (MvPowerSeries.constantCoeff f.val) ∧
      MvPowerSeries.gaussNorm (norm : K → ℝ) (fun _ : Fin r ↦ 1)
        (f - constants K r (MvPowerSeries.constantCoeff f.val)).val = 0) := by
  sorry

end RestrictedSeries
