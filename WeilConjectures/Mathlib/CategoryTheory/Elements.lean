/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Elements

/-!
# Categories of elements of universe enlarged and of isomorphic functors

If `F : C ⥤ Type w`, the category of elements of `F ⋙ uliftFunctor.{w', w}` is equivalent to
the category of elements of `F`: an element of `ULift (F.obj X)` is the same thing as an
element of `F.obj X`.

A natural isomorphism `F ≅ G` of functors `C ⥤ Type w` induces an equivalence
`F.Elements ≌ G.Elements` of the categories of elements. This is the isomorphism in `Cat`
obtained by applying `CategoryTheory.Functor.elementsFunctor`, read as an equivalence.

## Main definitions

- `CategoryTheory.Functor.Elements.uliftEquivalence`: the equivalence between the category of
  elements of a universe enlarged functor and the category of elements of the functor.
- `CategoryTheory.NatIso.mapElements`: the equivalence of categories of elements induced by
  a natural isomorphism.

-/

@[expose] public section

universe w' w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace Functor.Elements

/-- The category of elements of `F ⋙ uliftFunctor.{w', w}` is equivalent to the category of
elements of `F`. -/
@[simps!]
def uliftEquivalence (F : C ⥤ Type w) :
    (F ⋙ uliftFunctor.{w', w}).Elements ≌ F.Elements where
  functor.obj x := ⟨x.val.down⟩
  functor.map f := ⟨f.hom, congrArg ULift.down f.map_val⟩
  inverse.obj x := ⟨ULift.up x.val⟩
  inverse.map f := ⟨f.hom, congrArg ULift.up f.map_val⟩
  unitIso := Iso.refl _
  counitIso := Iso.refl _

end Functor.Elements

/-- A natural isomorphism of functors to types induces an equivalence between the categories
of elements, the functors in both directions being `CategoryTheory.NatTrans.mapElements`
applied to the two components of the isomorphism. -/
def NatIso.mapElements {F G : C ⥤ Type w} (e : F ≅ G) : F.Elements ≌ G.Elements :=
  Cat.equivOfIso (Functor.elementsFunctor.mapIso e)

end CategoryTheory
