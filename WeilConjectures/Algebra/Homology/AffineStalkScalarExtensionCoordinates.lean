/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.AffineOrdinaryTensorStalkCoordinates
public import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.RingTheory.Localization.BaseChange

/-! # Scalar extension coordinates for exact affine stalk homology

Source: Stacks Project, Tags 01I9 and 01AG.
(blueprint: lem-pc-affine-stalk-scalar-extension-coordinates). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
noncomputable section
namespace AlgebraicGeometry

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

end AlgebraicGeometry
