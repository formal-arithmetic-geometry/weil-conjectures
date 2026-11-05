/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PinnedPullbackCounitShifts
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.AlgebraicGeometry.PinnedPullbackCompositionShifts
import WeilConjectures.AlgebraicGeometry.PinnedDerivedAdjunctionShifts

/-! # Shift compatibility of the canonical derived base-change mate
Source: Stacks Project, Tag 08HY.
(blueprint: lem-pc-pinned-base-change-mate-shifts). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory
noncomputable section
namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency.types false

end AlgebraicGeometry
