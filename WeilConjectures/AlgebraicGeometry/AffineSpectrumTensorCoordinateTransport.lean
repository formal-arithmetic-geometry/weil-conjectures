/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.IsoPullbackStalkCohomology
public import WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionIso
public import WeilConjectures.AlgebraicGeometry.AffineSpectrumTensorCoherentCoordinateData

/-! # Affine coordinate transport of the localized tensor comparison

Source: Stacks Project, Tag 0DJ8, equation-bc and affine reduction; Tag 0098.
(blueprint: lem-pc-affine-spectrum-tensor-coordinate-transport).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
noncomputable section
namespace AlgebraicGeometry.SingleComplexBaseChange

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

attribute [local irreducible] isoPullbackAdditiveStalkIso
  Scheme.Modules.tensorPullbackCompositionIso

attribute [local irreducible] ordinaryIsoPullbackStalkComplexIso
  ordinaryIsoPullbackStalkHomologyIso

end AlgebraicGeometry.SingleComplexBaseChange
