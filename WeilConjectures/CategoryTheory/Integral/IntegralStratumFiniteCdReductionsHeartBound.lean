/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralQuotient.IntegralQuotientCoefficients
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension
public import WeilConjectures.CategoryTheory.Integral.IntegralStratumHomFormula
public import WeilConjectures.CategoryTheory.Integral.IntegralStratumFiniteCdReductionsHeartData
public import WeilConjectures.CategoryTheory.Integral.IntegralStratumFiniteCdReductionsSectionsFromData

/-! Heart-level section bound for the continuous integral coefficient.
(blueprint: lem-sfb-integral-stratum-finite-cd-reductions).

The proof transports the continuous coefficient to the normalized integral coefficient,
uses the finite local two-term resolution and the integral dual-torsion heart theorem,
and transports the resulting section bound back.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

attribute [local instance 20000] HasDerivedCategory.ofIsGrothendieckAbelian

namespace CategoryTheory

end CategoryTheory
