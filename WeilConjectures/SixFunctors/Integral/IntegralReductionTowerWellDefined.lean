/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Integral.IntegralDerivedReductionSupplement
public import WeilConjectures.AlgebraicGeometry.RestrictionOfScalarsExact
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.SixFunctors.Integral.IntegralReductionTowerWellDefinedUnrestricted

/-!
# Independence of the augmented integral reduction tower

Source: Stacks Project, sites-cohomology.tex, Tags 06YS/06YT/06YY; derived.tex,
Tags 05RT/06XN; Bhatt--Scholze, p. 24, Definition 3.5.2
(blueprint: lem-weil-integral-reduction-tower-well-defined).

The index n denotes exponent n+1. Pure tensors characterize the chain maps before
localization; the finite comparison is the composite of the recorded canonical
K-flat computation isomorphisms. No arbitrary comparison or transition is chosen.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe d t u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace WeilConjectures

-- Avoid unfolding the inverse limit and the constructed maps when identifying interfaces.
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence
  unrestrictedIntegralReductionExistence integralReductionExistence
  integralReductionDerivedExistence
  unrestrictedTowerUnit unrestrictedTowerTransition unrestrictedTowerResolutionIso
  unrestrictedTowerFiniteComparison unrestrictedTowerComparison

attribute [local instance] integralReductionChangeOfRingsAdditive

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (Y : AlgebraicGeometry.Scheme.{t})
  (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

attribute [local instance] integralTowerRestrictionLimits

attribute [local instance] integralTowerRestrictionColimits

end WeilConjectures
