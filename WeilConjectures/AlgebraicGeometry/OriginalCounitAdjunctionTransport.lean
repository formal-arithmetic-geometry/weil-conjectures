/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GlobalHomOriginalCounitNormalization
import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionNormalization

/-! # Transport of the adjunction to the original derived-pullback counit

Source: Stacks Project, Cohomology, Tag 06YJ; Derived Categories, Tag 09T5.
(blueprint: lem-pc-original-counit-adjunction-transport).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory
noncomputable section
namespace AlgebraicGeometry

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

end AlgebraicGeometry
