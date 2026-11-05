/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeMayerVietorisMaps
public import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisCanonicalData
import all WeilConjectures.AlgebraicGeometry.DerivedBaseChangeOpenRestriction
import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisOpenComparisonUnit

/-! # Transposition of the canonical base-change map for one open

Source: Stacks Project, Tags 08HY, 08FE and 0D5T.
(blueprint: lem-pc-derived-base-change-open-transpose).
-/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace AlgebraicGeometry
variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

end AlgebraicGeometry
