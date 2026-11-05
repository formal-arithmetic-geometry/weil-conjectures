/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Complete.CompleteProperOpenGamma
public import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerExchangeMateNormalization
public import WeilConjectures.CategoryTheory.Adjunction.ProperOpenTransport
import WeilConjectures.AlgebraicGeometry.Complete.CompleteStrictReductionComposition
import all WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerExchangeMateNormalization
import all WeilConjectures.AlgebraicGeometry.Completed.Open.CompletedOpenEndpointLimitTransport
import all WeilConjectures.AlgebraicGeometry.StrictTower.ScalarRestrictionOpenSupport
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenSlicePresentation
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategorySquareIsoSymm

/-!
# Strict reduction comparisons for completed operations

Strict reduction followed by constant-coefficient restriction compares completed-ring
objects with derived strict towers of constant-coefficient modules. This file records its
comparisons with inverse images.

Source: Weil conjectures blueprint, node thm-cbc-complete-proetale, proof step 8
(blueprint: thm-cbc-complete-proetale).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe t u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

end CategoryTheory

namespace CategoryTheory.ProperOpenTransport

end CategoryTheory.ProperOpenTransport

namespace AlgebraicGeometry.ProEtale.StrictTower

set_option backward.defeqAttrib.useBackward true

end AlgebraicGeometry.ProEtale.StrictTower

namespace AlgebraicGeometry.Scheme

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived flatConstantModulesAbelian
  SheafOfModules.RingedCoefficientProjection.cachedSheafifyModules
  SheafOfModules.RingedCoefficientProjection.cachedLocalEquivalences

attribute [local instance 100000] SheafOfModules.hasSheafify_coefficientUniverse
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse

end AlgebraicGeometry.Scheme
