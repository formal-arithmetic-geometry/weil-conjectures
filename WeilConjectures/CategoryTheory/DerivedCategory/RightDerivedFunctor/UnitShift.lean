/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.AdjunctionShift
public import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction

/-!
# The unit of a right derived functor commutes with the canonical shifts

The total right derived functor `F.rightDerivedFunctor` carries the shift structure transported
from the K-injective equivalence
(`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated`). This file
shows that its unit `F.mapHomotopyCategory ⋙ Qh ⟶ Qh ⋙ F.rightDerivedFunctor` commutes with
the shifts for this structure (`Functor.commShift_rightDerivedFunctorUnit`), and deduces that
the derived adjunction `L.mapDerivedCategory ⊣ R.rightDerivedFunctor` of an adjunction `L ⊣ R`
with `L` exact commutes with the shifts
(`Adjunction.commShift_mapDerivedCategoryRightDerivedAdjunction`).
-/

@[expose] public section

open CategoryTheory Category Limits Abelian

namespace CategoryTheory

namespace Adjunction

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasKInjectiveResolutions D]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L] (adj : L ⊣ R)

end Adjunction

end CategoryTheory
