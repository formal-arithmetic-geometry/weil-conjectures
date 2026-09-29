/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed
public import WeilConjectures.CategoryTheory.Monoidal.Instances.HomotopyCategory
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat

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

local instance : HasExactColimitsOfShape ℤ C :=
  have := AB5OfSize_of_univLE.{0, 0, w, w} C
  inferInstance

local instance (X : C) : PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X) :=
  preservesColimitsOfShape_of_natIso (BraidedCategory.tensorLeftIsoTensorRight X)

/-- For a braided monoidal closed Grothendieck abelian category with functorial flat
resolutions, the derived category is monoidal closed; this is `DerivedCategory.monoidalClosed`,
the K-flat derivability structure it asks for being provided by the flat resolutions. -/
noncomputable instance monoidalClosedOfMonoidalClosedBraidedCategory
    [Abelian.HasFunctorialFlatResolution C] :
    MonoidalClosed (DerivedCategory C) :=
  monoidalClosed C

end DerivedCategory
