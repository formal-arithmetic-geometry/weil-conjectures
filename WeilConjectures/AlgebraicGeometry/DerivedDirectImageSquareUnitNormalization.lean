/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisOpenCounitModel
public import WeilConjectures.AlgebraicGeometry.DerivedDirectImageCompositionUnit

/-! # A single derived unit across a commutative direct-image square

Source: Stacks Project, Cohomology, Tags 08FE and 0D5T.
(blueprint: lem-pc-direct-image-square-single-unit-normalization).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
noncomputable section
namespace AlgebraicGeometry

attribute [local instance 2000] schemeMVModuleAbelian

end AlgebraicGeometry
