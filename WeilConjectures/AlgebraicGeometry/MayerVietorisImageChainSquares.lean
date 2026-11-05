/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.MayerVietorisImageChainData
import WeilConjectures.AlgebraicGeometry.OpenImageDirectImageComparisonRestriction

/-! # Explicit restriction-induced comparison maps

Source: Stacks Project, Tags 08FE and 08BV.
(blueprint: def-pc-mayer-vietoris-image-chain-data).
-/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace Pretriangulated
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 2048
noncomputable section
namespace AlgebraicGeometry
attribute [local instance 2000] schemeMVModuleAbelian

attribute [local irreducible] schemeMVImageIso schemeOpenModuleImageRestriction
  schemeMVUnderivedOpenRestriction schemeMVUnderivedOpenComposition
  schemeOpenModuleAdjunction schemeOpenRestrictionCompIso

-- Use the proved degreewise API without unfolding the sectionwise map constructions.
attribute [local irreducible] schemeMVImageComponent
  schemeOpenModuleImageComplexRestriction

-- Keep the additive calculation abstract: its inputs are the proved map equations.

end AlgebraicGeometry
