/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PinnedPullbackCounitShifts
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors

/-! # Shift compatibility of the pinned tensor counit on singles
Source: Stacks Project, Tags 08HY and 0D5S; Mathlib single-functor shifts.
(blueprint: lem-pc-pinned-single-tensor-shifts). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Functor
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CategoryTheory.SingleFunctors

end CategoryTheory.SingleFunctors

namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency.types false

end AlgebraicGeometry
