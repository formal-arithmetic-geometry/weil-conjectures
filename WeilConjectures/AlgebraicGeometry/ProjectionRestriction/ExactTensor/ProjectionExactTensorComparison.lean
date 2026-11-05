/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectionRestriction.ProjectionExactTensorCore
import WeilConjectures.AlgebraicGeometry.ProjectionRestriction.ExactTensor.ProjectionExactTensorFirstShift
import WeilConjectures.AlgebraicGeometry.ProjectionRestriction.ExactTensor.ProjectionExactTensorSecondShift

/-! Exact tensor functors on resolving representatives.
Source: Stacks Project, Tags 06YU, 07A4 and 0FNH.
(blueprint: lem-weil-pbc-projection-exact-tensor-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
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

end ExactTensor
end AlgebraicGeometry.Scheme.ProjectionRestriction
