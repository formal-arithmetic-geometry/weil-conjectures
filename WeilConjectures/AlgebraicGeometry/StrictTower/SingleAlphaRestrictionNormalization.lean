/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerOrdinaryProperOpenArrows
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerOrdinaryProperOpenArrows
import all WeilConjectures.AlgebraicGeometry.StrictTower.TowerOpenBetaNormalization
import all WeilConjectures.CategoryTheory.SmoothPurity.ProperOpenCompositeTransformation

/-! # Restriction of intrinsic proper/open alpha

Source: Stacks Project, Tags 09BN and 0F7C, with the arbitrary-ring underived refinement.
(blueprint: lem-cbc-single-alpha-restriction-normalization)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option Elab.async false
set_option synthInstance.maxSize 2048
set_option linter.unusedSimpArgs false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.StrictTower
variable (B : Type (u + 1)) [CommRing B]

attribute [local irreducible] Functor.leftAdjoint modulePullback singleAlpha moduleGComp
  moduleSquareG moduleJAdj clopenModulePi openBetaModule openBetaModuleJComp
  singleJCongr

end AlgebraicGeometry.ProEtale.StrictTower
