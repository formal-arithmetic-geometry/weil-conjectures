/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RelativeMVInverseOpenIso
import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeOpenUnit
import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionUnitIso

/-! # Coefficient comparison for an inverse-image open

Source: Stacks Project, Cohomology, Tags 08HY and 0D5S.
(blueprint: lem-pc-relative-mv-open-coefficient-transport).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry

variable [d : ∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

end AlgebraicGeometry
