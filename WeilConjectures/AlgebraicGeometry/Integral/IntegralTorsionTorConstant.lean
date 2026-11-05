/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcRationalCategory
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectModelsSupplement
public import WeilConjectures.RingTheory.QuotientLevelTor
import WeilConjectures.AlgebraicGeometry.Integral.IntegralLevelConstantRestriction
import all WeilConjectures.AlgebraicGeometry.CompletedConstantReduction.CompletedConstantSheafReductionSupplement
import all WeilConjectures.AlgebraicGeometry.Perfect.PerfectChartTensorComparison
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralCompletedLocalPerfectCriterion
import WeilConjectures.AlgebraicGeometry.Completed.CompletedRealizationDerivedCohomology
import WeilConjectures.FromJoel.Algebra.Homology.PreservesQuasiIso
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# The consecutive-quotient Tor sheaf of a constant perfect complex

For a perfect complex `C` over the valuation ring `A`, the degree-`q` cohomology of the
`n+1`-st reduction of its constant realization is the constant sheaf of the module
`M = H^q(C ⊗ A/π^{n+2})`, and the consecutive-quotient Tor sheaf of a constant sheaf is
the constant sheaf of the module-level Tor. A torsion summand `N₀` of `H^q(C)` is a retract
of `M`, which gives the surjection onto `N₀/πN₀`.

Source: Bhatt--Scholze, Proposition 6.6.11; step 5 of
`lem-weil-pbc-adic-tor-implies-flat-cohomology`
(blueprint: lem-weil-pbc-integral-cohomology-torsion-normal-form).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

-- `surjectiveTower_wEqualsLocallyBijective` leaves its coefficient universe free
attribute [-instance] AlgebraicGeometry.ProEtale.surjectiveTower_wEqualsLocallyBijective

section Sheaf

variable (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

end Sheaf

end AlgebraicGeometry.Scheme
