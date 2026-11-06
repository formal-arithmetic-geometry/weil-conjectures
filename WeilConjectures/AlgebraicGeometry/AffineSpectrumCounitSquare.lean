/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineSpectrumDerivedCoordinates
public import WeilConjectures.AlgebraicGeometry.AffineSpectrumOrdinaryComparisonSquare
import WeilConjectures.AlgebraicGeometry.AffineSpectrumCompositionCounitSquare

/-! # The affine spectrum derived counit square

Source: Stacks Project, Tag 0DJ8, equation-bc and affine reduction; Tag 0098.
(blueprint: lem-pc-affine-spectrum-counit-square).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace AlgebraicGeometry.SingleComplexBaseChange

attribute [local instance_reducible] Scheme.Modules TopCat.Sheaf
attribute [local implicit_reducible] DerivedCategory
  HomotopyCategory DerivedCategory.Q DerivedCategory.Qh

end AlgebraicGeometry.SingleComplexBaseChange
