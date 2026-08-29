/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# The tensor product of sheaves is preadditive

Let `A` be an abelian monoidal category whose tensor product is additive in each variable
and `J` a Grothendieck topology with `HasSheafify J A` such that the localized monoidal
structure `Sheaf.monoidalCategory` on `Sheaf J A` is available (`(J.W).IsMonoidal`).
We show that this monoidal structure is compatible with the preadditive structure on
`Sheaf J A`, i.e. `MonoidalPreadditive (Sheaf J A)`.

The key observation is that tensoring with a fixed sheaf `X` is, up to a natural
isomorphism, computed by tensoring the underlying presheaves and sheafifying
(`Sheaf.tensorLeftIso`/`Sheaf.tensorRightIso`); additivity then transfers from the
pointwise tensor product of presheaves and the additivity of sheafification.

## Main results

- `CategoryTheory.Sheaf.monoidalPreadditive`: the monoidal category structure on
  `Sheaf J A` obtained in `Sheaf.monoidalCategory` is preadditive.
-/

@[expose] public section

universe v₁ v₃ u₁ u₃

namespace CategoryTheory.Sheaf

open MonoidalCategory Functor

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {A : Type u₃} [Category.{v₃} A] [MonoidalCategory A] [Abelian A] [MonoidalPreadditive A]
  [HasSheafify J A] [(J.W (A := A)).IsMonoidal]

attribute [local instance] monoidalCategory

/-- The isomorphism `L P ⊗ L Q ≅ L (P ⊗ Q)` for sheafification `L`, as a natural
isomorphism `presheafToSheaf J A ⋙ tensorLeft ((presheafToSheaf J A).obj P) ≅
tensorLeft P ⋙ presheafToSheaf J A` in the second variable. -/
noncomputable def presheafToSheafCompTensorLeftIso (P : Cᵒᵖ ⥤ A) :
    presheafToSheaf J A ⋙ tensorLeft ((presheafToSheaf J A).obj P) ≅
      tensorLeft P ⋙ presheafToSheaf J A :=
  NatIso.ofComponents (fun Q ↦ Functor.Monoidal.μIso (presheafToSheaf J A) P Q)
    (fun _ ↦ by simp)

/-- The isomorphism `L P ⊗ L Q ≅ L (P ⊗ Q)` for sheafification `L`, as a natural
isomorphism `presheafToSheaf J A ⋙ tensorRight ((presheafToSheaf J A).obj Q) ≅
tensorRight Q ⋙ presheafToSheaf J A` in the first variable. -/
noncomputable def presheafToSheafCompTensorRightIso (Q : Cᵒᵖ ⥤ A) :
    presheafToSheaf J A ⋙ tensorRight ((presheafToSheaf J A).obj Q) ≅
      tensorRight Q ⋙ presheafToSheaf J A :=
  NatIso.ofComponents (fun P ↦ Functor.Monoidal.μIso (presheafToSheaf J A) P Q)
    (fun _ ↦ by simp)

/-- Tensoring on the left with a sheaf `X` is, up to natural isomorphism, computed by
tensoring the underlying presheaves with `X.obj` and sheafifying. -/
noncomputable def tensorLeftIso (X : Sheaf J A) :
    tensorLeft X ≅ sheafToPresheaf J A ⋙ tensorLeft X.obj ⋙ presheafToSheaf J A :=
  (curriedTensor (Sheaf J A)).mapIso
      (asIso ((sheafificationAdjunction J A).counit.app X)).symm ≪≫
    (tensorLeft _).leftUnitor.symm ≪≫
    isoWhiskerRight (asIso (sheafificationAdjunction J A).counit).symm _ ≪≫
    associator _ _ _ ≪≫
    isoWhiskerLeft (sheafToPresheaf J A) (presheafToSheafCompTensorLeftIso X.obj)

/-- Tensoring on the right with a sheaf `X` is, up to natural isomorphism, computed by
tensoring the underlying presheaves with `X.obj` and sheafifying. -/
noncomputable def tensorRightIso (X : Sheaf J A) :
    tensorRight X ≅ sheafToPresheaf J A ⋙ tensorRight X.obj ⋙ presheafToSheaf J A :=
  (curriedTensor (Sheaf J A)).flip.mapIso
      (asIso ((sheafificationAdjunction J A).counit.app X)).symm ≪≫
    (tensorRight _).leftUnitor.symm ≪≫
    isoWhiskerRight (asIso (sheafificationAdjunction J A).counit).symm _ ≪≫
    associator _ _ _ ≪≫
    isoWhiskerLeft (sheafToPresheaf J A) (presheafToSheafCompTensorRightIso X.obj)

noncomputable instance (X : Sheaf J A) : (tensorLeft X).Additive :=
  Functor.additive_of_iso (tensorLeftIso X).symm

noncomputable instance (X : Sheaf J A) : (tensorRight X).Additive :=
  Functor.additive_of_iso (tensorRightIso X).symm

/-- The monoidal category structure on `Sheaf J A` obtained in `Sheaf.monoidalCategory`
is preadditive when `A` is an abelian monoidal category with additive tensor product. -/
instance monoidalPreadditive : MonoidalPreadditive (Sheaf J A) where
  whiskerLeft_zero {X Y Z} := (tensorLeft X).map_zero Y Z
  zero_whiskerRight {X Y Z} := (tensorRight X).map_zero Y Z
  whiskerLeft_add {X _ _} _ _ := (tensorLeft X).map_add
  add_whiskerRight {X _ _} _ _ := (tensorRight X).map_add

end CategoryTheory.Sheaf
