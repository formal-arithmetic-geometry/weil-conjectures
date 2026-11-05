/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.AffineTildeTensorSourceComparison
public import WeilConjectures.Algebra.Homology.AffineBaseChangeTildeRepresentative
import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeUnitCompatibility
public import WeilConjectures.Algebra.Homology.AffineTildeTensorOrdinaryExchangePreNormalization

/-! # Ordinary affine exchange in tensor coordinates

Source: Stacks Project, Tags 01I9, 06Y6 and 08HY.
(blueprint: lem-pc-affine-tilde-tensor-ordinary-exchange).
-/

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
