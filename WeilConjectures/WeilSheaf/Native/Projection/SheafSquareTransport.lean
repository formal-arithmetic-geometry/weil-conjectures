/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.MatesHCompIsIso
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra
public import Mathlib.CategoryTheory.Monoidal.Category

/-! # Abstract identities for transporting the sheaf tensor square -/

@[expose] public section

open CategoryTheory MonoidalCategory

namespace CategoryTheory

/-- Forgetting the structure of an iso-algebra contributes an identity to a horizontal square. -/
lemma Endofunctor.IsoAlgebra.isoHComp_forget_symm_hom_app
    {C D A B : Type*} [Category C] [Category D] [Category A] [Category B]
    {F : C ⥤ C} {G : D ⥤ D} {L : C ⥤ D} (e : L ⋙ G ≅ F ⋙ L)
    {T : C ⥤ A} {R : A ⥤ B} {V : D ⥤ B} (b : T ⋙ R ≅ L ⋙ V)
    (M : Endofunctor.IsoAlgebra F) :
    (Functor.isoHComp (Endofunctor.IsoAlgebra.mapOfNatIsoCompForgetIso e).symm b).hom.app M =
      b.hom.app M.carrier := by
  rw [Functor.isoHComp_hom_app]
  simp only [Endofunctor.IsoAlgebra.mapOfNatIsoCompForgetIso,
    Iso.symm_hom, Iso.refl_inv, NatTrans.id_app]
  erw [Functor.map_id, Category.comp_id]

/-- Rotate an invertible tensor comparison square to the opposite orientation. -/
lemma tensorSquare_rotate {C : Type*} [Category C] [MonoidalCategory C]
    {W W' X Y A A' B B' : C} (b : W ≅ W') (a : W ≅ X) (u : X ⟶ Y)
    (n : Y ≅ B ⊗ B') (am : A ≅ B) (an : A' ≅ B') (d : W' ⟶ A ⊗ A')
    (h : b.inv ≫ a.hom ≫ u = d ≫ (am.hom ⊗ₘ an.hom) ≫ n.inv) :
    u ≫ n.hom ≫ (am.inv ⊗ₘ an.inv) = a.inv ≫ b.hom ≫ d := by
  apply (cancel_epi a.hom).1
  apply (cancel_epi b.inv).1
  simp only [Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc]
  rw [reassoc_of% h]
  simp only [Iso.inv_hom_id_assoc, tensorHom_comp_tensorHom,
    Iso.hom_inv_id, id_tensorHom_id, Category.comp_id]

end CategoryTheory
