/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed
public import WeilConjectures.CategoryTheory.Monoidal.Instances.HomotopyCategory
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfSize
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic

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

section

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

end

variable [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]

/-- If `C` is braided and has functorial flat resolutions, K-flat complexes form a left
derivability structure, so `DerivedCategory.monoidalClosed` applies. -/
noncomputable instance monoidalClosed_of_hasFunctorialFlatResolution
    [Abelian.HasFunctorialFlatResolution C] :
    MonoidalClosed (DerivedCategory C) :=
  monoidalClosed C

end DerivedCategory
