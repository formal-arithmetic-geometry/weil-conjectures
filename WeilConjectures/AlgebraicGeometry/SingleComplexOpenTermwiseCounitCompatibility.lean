/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenTensorRestrictionIso
import WeilConjectures.AlgebraicGeometry.OpenPinnedCounitHomotopyRestriction

/-! # Compatibility of open restriction with the pinned pullback counits

Source: Stacks Project, cohomology.tex, Tags 08HY, 08FE and 0D5S.
(blueprint: lem-pc-single-complex-open-counit-compatibility).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AlgebraicGeometry
open SingleComplexBaseChange
set_option synthInstance.maxSize 2048

end AlgebraicGeometry
