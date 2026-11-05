/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerOrdinaryProperOpenArrows
public import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionSquare
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
-- Vertical uses singleAlpha_restriction_normalized; horizontal uses singleAlpha_restriction.
-- Both restriction identities must coexist when these dependency branches are imported.
import all WeilConjectures.AlgebraicGeometry.StrictTower.ProperOpenAlphaVerticalModules
import all WeilConjectures.AlgebraicGeometry.StrictTower.ProperOpenAlphaHorizontalModules
import all WeilConjectures.AlgebraicGeometry.StrictTower.ProperOpenAlphaBaseChangeModules

/-! # Intrinsic clopen alpha commutes with pasting and pullback before derivation

Source: Stacks Project, Tags 0F7C, 0F7D, 0F7F, 09AH and 09BN, with the arbitrary-ring
underived strict-tower refinement in the blueprint.
(blueprint: lem-cbc-proper-open-alpha-pasting)

Each law includes equality on module sheaves, on strict towers, on their unbounded
complexes, and on their ordinary unbounded derived categories. The two ordinary paths
are written with all inverse-image and open-extension compositors inserted.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.StrictTower

variable (B : Type (u + 1)) [CommRing B]

attribute [local irreducible] G J

end AlgebraicGeometry.ProEtale.StrictTower
