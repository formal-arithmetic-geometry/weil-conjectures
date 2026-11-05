/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerOrdinaryProperOpenArrows
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerOrdinaryProperOpenArrows
import all WeilConjectures.AlgebraicGeometry.StrictTower.TowerOpenBetaNormalization

/-! # Restriction of the intrinsic proper/open arrow

Source: Stacks, Tags 09BN and 0F7B; restriction calculation in steps 2--3 of
`lem-cbc-proper-open-alpha-horizontal-modules`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types true
set_option linter.unusedSimpArgs false

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale.StrictTower

variable (B : Type (u + 1)) [CommRing B]

attribute [local irreducible] Functor.leftAdjoint modulePullback moduleGComp
attribute [local irreducible] moduleSquareG openBetaModule openBetaModuleJComp
attribute [local irreducible] singleAlpha clopenModulePi singleJCongr moduleOpenUnitInv
attribute [local irreducible] moduleJAdj

-- Keep the chosen composition comparisons abstract during the calculation.

-- Apply the calculation to an arbitrary clopen factorization of alpha.

end AlgebraicGeometry.ProEtale.StrictTower
