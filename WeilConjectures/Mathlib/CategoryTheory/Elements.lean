/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Elements

/-!
# The category of elements of a universe enlarged functor

If `F : C ⥤ Type w`, the category of elements of `F ⋙ uliftFunctor.{w', w}` is equivalent to
the category of elements of `F`: an element of `ULift (F.obj X)` is the same thing as an
element of `F.obj X`.
-/

@[expose] public section

universe w' w v u

namespace CategoryTheory.Functor.Elements

variable {C : Type u} [Category.{v} C]

/-- The category of elements of `F ⋙ uliftFunctor.{w', w}` is equivalent to the category of
elements of `F`. -/
@[simps]
def uliftEquivalence (F : C ⥤ Type w) :
    (F ⋙ uliftFunctor.{w', w}).Elements ≌ F.Elements where
  functor.obj x := ⟨x.1, x.2.down⟩
  functor.map f := ⟨f.1, congrArg ULift.down f.2⟩
  inverse.obj x := ⟨x.1, ULift.up x.2⟩
  inverse.map f := ⟨f.1, congrArg ULift.up f.2⟩
  unitIso := Iso.refl _
  counitIso := Iso.refl _

lemma uliftEquivalence_functor_comp_π (F : C ⥤ Type w) :
    (uliftEquivalence.{w'} F).functor ⋙ CategoryOfElements.π F =
      CategoryOfElements.π (F ⋙ uliftFunctor.{w', w}) :=
  rfl

end CategoryTheory.Functor.Elements
