/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeMayerVietorisCanonicalData
import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeMayerVietorisCanonicalShift
import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeMayerVietorisCanonicalPullback
import WeilConjectures.AlgebraicGeometry.OpenImageComplexComparisonUnit
import WeilConjectures.AlgebraicGeometry.OpenImageComplexComparisonRestriction

/-! Intermediate existence data for the relative Mayer--Vietoris boundary.
Source: Stacks Project, Tags 08BV and 0DJ9.
(blueprint: lem-pc-rf-mv-base-change-connecting-square-data).
-/
@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace Pretriangulated
set_option autoImplicit false
noncomputable section
namespace AlgebraicGeometry

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

end AlgebraicGeometry
