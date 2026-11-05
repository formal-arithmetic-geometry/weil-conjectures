/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
import WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift

/-! # Shifts compatible with the composition-pinned pullback counits
Source: Stacks Project, Tags 08HY and 0D5S.
(blueprint: lem-pc-pinned-pullback-counit-shifts). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory
noncomputable section
namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency.types false

end AlgebraicGeometry
