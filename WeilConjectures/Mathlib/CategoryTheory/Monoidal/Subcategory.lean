/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Monoidal.Subcategory

/-!
# Restrictions of monoidal functors to full monoidal subcategories

Let `P` and `Q` be monoidal properties of objects of monoidal categories `C` and `D`, and
`F : C ⥤ D` a strong monoidal functor sending objects satisfying `P` to objects satisfying `Q`.
The restriction `Q.lift (P.ι ⋙ F) hF : P.FullSubcategory ⥤ Q.FullSubcategory` is then strong
monoidal, with the comparison isomorphisms of `F`.

## Main definitions

- `CategoryTheory.ObjectProperty.monoidalLift`: the strong monoidal structure on the
  restriction of a strong monoidal functor to full monoidal subcategories.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.ObjectProperty

open MonoidalCategory Functor.LaxMonoidal

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  {P : ObjectProperty C} [P.IsMonoidal] {Q : ObjectProperty D} [Q.IsMonoidal]
  (F : C ⥤ D) [F.Monoidal] (hF : ∀ X : P.FullSubcategory, Q (F.obj X.obj))

/-- The restriction `Q.lift (P.ι ⋙ F)` of a strong monoidal functor `F` to full monoidal
subcategories is strong monoidal, with the comparison isomorphisms of `F`. -/
noncomputable instance monoidalLift : (Q.lift (P.ι ⋙ F) hF).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Q.fullyFaithfulι.preimageIso (Functor.Monoidal.εIso F)
      μIso X Y := Q.fullyFaithfulι.preimageIso (Functor.Monoidal.μIso F X.obj Y.obj)
      μIso_hom_natural_left f X' := hom_ext _ (μ_natural_left F f.hom X'.obj)
      μIso_hom_natural_right X' f := hom_ext _ (μ_natural_right F X'.obj f.hom)
      associativity X Y Z := hom_ext _ (associativity F X.obj Y.obj Z.obj)
      left_unitality X := hom_ext _ (left_unitality F X.obj)
      right_unitality X := hom_ext _ (right_unitality F X.obj) }

end CategoryTheory.ObjectProperty
