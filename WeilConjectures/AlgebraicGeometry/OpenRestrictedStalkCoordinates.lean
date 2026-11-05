/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
import WeilConjectures.AlgebraicGeometry.OpenDerivedStalkIso
import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
/-! # Normalized ring and input-stalk coordinates

Source: Stacks Project, Tag 0098, stalks of pullback and restriction.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
noncomputable section
namespace AlgebraicGeometry
open TopologicalSpace Opposite
set_option synthInstance.maxSize 2048

end AlgebraicGeometry

namespace AlgebraicGeometry.SingleComplexBaseChange
variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

end AlgebraicGeometry.SingleComplexBaseChange
