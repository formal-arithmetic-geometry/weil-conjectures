/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerOpenExtension
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenSlicePresentation
import Mathlib.CategoryTheory.Adjunction.Triple

/-! # Scalar restriction preserves ordinary open support

Source: Stacks Project, Modules on Sites, Tag 03DI, the sheafified direct-sum
construction of extension by zero (blueprint: lem-sf-scalar-restriction-open-support).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory

namespace AlgebraicGeometry.ProEtale.StrictTower

set_option backward.defeqAttrib.useBackward true

end AlgebraicGeometry.ProEtale.StrictTower
