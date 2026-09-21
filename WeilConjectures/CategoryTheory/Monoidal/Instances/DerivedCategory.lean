/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed
public import WeilConjectures.CategoryTheory.Monoidal.Instances.HomotopyCategory

/-!

# Shortcut instances for monoidal derived category

-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

universe w v u

namespace DerivedCategory

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

local instance : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink C

variable [HasDerivedCategory.{w} C]

variable [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
  [Qh.HasDerivedMonoidalCategory (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]

noncomputable instance monoidalCategoryOfMonoidalClosedBraidedCategory :
  MonoidalCategory (DerivedCategory C) := inferInstance

noncomputable instance laxMonoidalQh : (Qh (C := C)).LaxMonoidal := inferInstance

instance isLeftDerivedFunctor₂CurriedTensor :
  (curriedTensor (DerivedCategory C)).IsLeftDerivedFunctor₂
    (Functor.LaxMonoidal.μNatTrans Qh) (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) := inferInstance

noncomputable instance laxMonoidalQ : (Q (C := C)).LaxMonoidal := inferInstance

noncomputable instance monoidalClosedOfMonoidalClosedBraidedCategorg :
  MonoidalClosed (DerivedCategory C) := DerivedCategory.monoidalClosed C

end DerivedCategory
