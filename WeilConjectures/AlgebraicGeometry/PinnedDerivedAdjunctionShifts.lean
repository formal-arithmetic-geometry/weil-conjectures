/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PinnedPullbackCounitShifts
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.CategoryTheory.Shift.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift

/-! # Shift compatibility of the selected derived adjunction
Source: Stacks Project, Tags 08HY and 0D5S. -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory
noncomputable section

-- Transport the unit along the K-injective equivalence, then detect it on resolutions.

-- Normalization identifies the left-derived counit with the inverse mate of the right unit.

-- Shift equivalences preserve the Kan universal property, which detects each comparison.

namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency.types false

end AlgebraicGeometry
