/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisOpenCounitModel
import all WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisOpenComparisonUnit
import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisUnderivedOpenCounitSquare

/-! # The ordinary open-image comparison and its unit

Source: Stacks Project, Cohomology, Tags 08FE and 08BV.
(blueprint: lem-pc-open-image-direct-image-comparison-unit).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace AlgebraicGeometry

attribute [local irreducible] schemeMVUnderivedOpenComposition
  schemeMVUnderivedOpenRestriction schemeOpenModuleAdjunction RingedSpace.moduleDirectImage

end AlgebraicGeometry
