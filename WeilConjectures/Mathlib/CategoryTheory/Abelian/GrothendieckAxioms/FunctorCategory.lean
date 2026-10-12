/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Generator.Presheaf

/-!
# Presheaf categories with values in a Grothendieck abelian category

If `A` is a Grothendieck abelian category (relative to a universe `w`) and `C` is a small
category with objects and morphisms in `Type`, for instance `ℕ`, then the category
`Cᵒᵖ ⥤ A` of `A`-valued presheaves on `C` is again Grothendieck abelian: colimits and their
exactness are computed objectwise, and a separator is given by the coproduct of the free
presheaves `Presheaf.freeYoneda X G` on a separator `G` of `A`.

The intended application is the category `ℕᵒᵖ ⥤ A` of towers in `A`.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Limits

variable (C : Type) [SmallCategory C] (A : Type u) [Category.{v} A]

/-- Presheaves on a category whose objects and morphisms live in `Type` with values in a
locally `w`-small category form a locally `w`-small category: a natural transformation is
determined by its components. -/
instance Presheaf.locallySmall [LocallySmall.{w} A] : LocallySmall.{w} (Cᵒᵖ ⥤ A) where
  hom_small P Q := small_of_injective (f := fun (f : P ⟶ Q) (X : Cᵒᵖ) ↦ f.app X)
    (fun f g h ↦ by ext X; exact congr_fun h X)

/-- A presheaf category `Cᵒᵖ ⥤ A` on a category with objects and morphisms in `Type` is
Grothendieck abelian when `A` is. -/
instance Presheaf.isGrothendieckAbelian [Abelian A] [IsGrothendieckAbelian.{w} A] :
    IsGrothendieckAbelian.{w} (Cᵒᵖ ⥤ A) where
  hasFilteredColimitsOfSize := ⟨fun _ _ _ ↦ inferInstance⟩
  ab5OfSize := ⟨fun _ _ _ ↦ inferInstance⟩
  hasSeparator := by
    have : HasColimitsOfSize.{0, 0} A := hasColimitsOfSizeShrink.{0, 0, w, w} A
    exact Presheaf.hasSeparator C A

end CategoryTheory
