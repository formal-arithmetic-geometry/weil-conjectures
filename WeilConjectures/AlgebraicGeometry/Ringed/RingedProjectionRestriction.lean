/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionRestrictionDataSupplement
import WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionGlobalModel
import WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionLocalModel
import WeilConjectures.Algebra.Homology.Ringed.RingedRestrictionLocalIso

/-! # Canonical localization comparisons for the projection mate

Source: Stacks Project, Tags 04J0, 08FI, 07A4, 0B56 and 0944.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme
open ProjectionRestriction
end AlgebraicGeometry.Scheme
