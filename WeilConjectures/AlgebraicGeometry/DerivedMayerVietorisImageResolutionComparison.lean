/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisCanonicalData
public import WeilConjectures.AlgebraicGeometry.DerivedDirectImageSplitTriangle
import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisImageResolutionComparisonIntersection

/-! # Comparing the concrete Mayer--Vietoris sequences after direct image

Source: Stacks Project, Tags 08BV, 08FE and 0D5T.
(blueprint: lem-pc-mayer-vietoris-image-resolution-comparison).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace Pretriangulated

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

noncomputable section
namespace AlgebraicGeometry

attribute [local instance 2000] schemeMVModuleAbelian

end AlgebraicGeometry
