/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeMayerVietorisCanonicalData
import WeilConjectures.AlgebraicGeometry.PinnedBaseChangeMateShifts
import WeilConjectures.AlgebraicGeometry.PinnedDerivedAdjunctionShifts

/-! Canonical compatibility for relative Mayer--Vietoris.
Source: Stacks Project, Tags 08BV, 08HY and 0DJ9. -/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace Pretriangulated
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace AlgebraicGeometry
variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

end AlgebraicGeometry
