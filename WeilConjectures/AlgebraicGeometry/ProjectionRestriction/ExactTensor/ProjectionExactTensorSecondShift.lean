/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectionRestriction.ProjectionExactTensorCore
import all WeilConjectures.AlgebraicGeometry.ProjectionRestriction.ProjectionExactTensorCore
import all WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionTensorShifts

/-! Signed shift verification for exact tensor descent.
Source: Stacks 07A4 and 0FNH.
(blueprint: lem-weil-pbc-projection-exact-tensor-shift-second).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.privateModule false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Scheme.ProjectionRestriction

variable {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
  [EssentiallySmall.{u + 1} C] [EssentiallySmall.{u + 1} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {R : Sheaf J CommRingCat.{u + 1}} {S : Sheaf K CommRingCat.{u + 1}}

namespace ExactTensor
attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [local semireducible] ObjectProperty.hasShift ObjectProperty.commShiftι
attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors

end ExactTensor
end AlgebraicGeometry.Scheme.ProjectionRestriction
