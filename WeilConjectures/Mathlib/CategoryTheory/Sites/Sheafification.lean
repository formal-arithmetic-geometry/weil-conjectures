/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Sites.Sheafification

/-!

# Morphisms from a sheaf to the sheafification of a presheaf

Let `J` be a Grothendieck topology on `C` and `A` a category with `J`-sheafification. A morphism
of presheaves `g : S.obj ⟶ P` from the presheaf underlying a sheaf `S` to a presheaf `P` induces
a morphism of sheaves `S ⟶ sheafify P`, by composing the inverse of the counit isomorphism
`sheafify S.obj ≅ S` with the sheafification of `g`. Its underlying morphism of presheaves is
`g ≫ toSheafify P`. This is used to define the morphisms `E ⟶ ℚ̄_ℓ` from the condensed rings
`C(-, E)` to the sheafification `ℚ̄_ℓ` of their union.

-/

@[expose] public section

universe v u w v'

open CategoryTheory Limits

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) {A : Type w} [Category.{v'} A]
  [HasWeakSheafify J A]

/-- The counit of the sheafification adjunction at a sheaf `S` is an isomorphism
`sheafify S.obj ≅ S`. -/
noncomputable def sheafifyObjIso (S : Sheaf J A) : (presheafToSheaf J A).obj S.obj ≅ S :=
  asIso ((sheafificationAdjunction J A).counit.app S)

variable {J}

/-- The morphism of sheaves `S ⟶ sheafify P` induced by a morphism of presheaves `S.obj ⟶ P`. -/
noncomputable def homToSheafify {S : Sheaf J A} {P : Cᵒᵖ ⥤ A} (g : S.obj ⟶ P) :
    S ⟶ (presheafToSheaf J A).obj P :=
  (sheafifyObjIso J S).inv ≫ (presheafToSheaf J A).map g

/-- The presheaf morphism underlying the inverse of the counit isomorphism `sheafify S.obj ≅ S`
is the unit `toSheafify S.obj`. -/
lemma sheafToPresheaf_map_sheafifyObjIso_inv (S : Sheaf J A) :
    (sheafToPresheaf J A).map (sheafifyObjIso J S).inv = toSheafify J S.obj := by
  rw [← cancel_mono ((sheafToPresheaf J A).map (sheafifyObjIso J S).hom), ← Functor.map_comp,
    Iso.inv_hom_id, Functor.map_id]
  exact ((sheafificationAdjunction J A).right_triangle_components S).symm

/-- The morphism of presheaves underlying `homToSheafify g` is `g ≫ toSheafify P`. -/
lemma homToSheafify_hom {S : Sheaf J A} {P : Cᵒᵖ ⥤ A} (g : S.obj ⟶ P) :
    (homToSheafify g).hom = g ≫ toSheafify J P := by
  change (sheafifyObjIso J S).inv.hom ≫ ((presheafToSheaf J A).map g).hom = _
  change (sheafToPresheaf J A).map _ ≫ (sheafToPresheaf J A).map _ = _
  rw [sheafToPresheaf_map_sheafifyObjIso_inv]
  exact ((sheafificationAdjunction J A).unit.naturality g).symm

/-- Precomposing `homToSheafify g` with a morphism of sheaves `f : S' ⟶ S` gives
`homToSheafify (f.hom ≫ g)`. -/
lemma comp_homToSheafify {S' S : Sheaf J A} {P : Cᵒᵖ ⥤ A} (f : S' ⟶ S) (g : S.obj ⟶ P) :
    f ≫ homToSheafify g = homToSheafify (f.hom ≫ g) := by
  unfold homToSheafify
  rw [Functor.map_comp, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [sheafifyObjIso, sheafifyObjIso, asIso_inv, asIso_inv, IsIso.comp_inv_eq, Category.assoc,
    IsIso.eq_inv_comp]
  exact ((sheafificationAdjunction J A).counit.naturality f).symm

/-- The sheafification of `g : S.obj ⟶ P` is conjugate to `homToSheafify g` by the counit
isomorphism. -/
lemma presheafToSheaf_map_eq_sheafifyObjIso_hom_comp {S : Sheaf J A} {P : Cᵒᵖ ⥤ A}
    (g : S.obj ⟶ P) :
    (presheafToSheaf J A).map g = (sheafifyObjIso J S).hom ≫ homToSheafify g := by
  unfold homToSheafify
  rw [Iso.hom_inv_id_assoc]

end CategoryTheory.Sheaf
