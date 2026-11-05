/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Constant.ConstantScalarRestrictionTensorSupplement
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap

/-! # Normalized derived tensor and projection comparison squares

Source: Stacks Project, Cohomology on Sites, Tags 07A4 and 07A6
(blueprint: def-sfb-derived-projection-comparison-squares).

These predicates expand the tensor, localization and adjunction-transpose squares.
They impose equations on the specified comparisons, without choosing maps.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
universe a b c e ha hb hc he wa wb wt
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace CategoryTheory.ConstantModuleDerivedProjection

end CategoryTheory.ConstantModuleDerivedProjection
