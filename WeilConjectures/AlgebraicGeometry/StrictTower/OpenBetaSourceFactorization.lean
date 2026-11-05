/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenArrows
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerDirectImageCoherence
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerPullbackSquarePasting

/-!
# Source factorization of the normalized inverse open comparison

Source: Stacks, Tags 03DI, 07A7 and 0F7B; the source-factorization calculation in
step 8 of (blueprint: lem-cbc-proper-open-clopen-projector).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.StrictTower
variable (B : Type (u + 1)) [CommRing B]

set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048
attribute [local irreducible] G gComp gCompEq squareG towers_hasDerivedCategory

end AlgebraicGeometry.ProEtale.StrictTower
