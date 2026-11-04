/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.MatesHCompIsIso
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.Functor
public import WeilConjectures.CategoryTheory.Functor.CurryComparison

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
  rfl

/-- The inverse spelling avoids reducing a concrete conjugate isomorphism. -/
lemma Endofunctor.IsoAlgebra.isoHComp_forget_symm_inv_hom_app
    {C D A B : Type*} [Category C] [Category D] [Category A] [Category B]
    {F : C ⥤ C} {G : D ⥤ D} {L : C ⥤ D} (e : L ⋙ G ≅ F ⋙ L)
    {T : C ⥤ A} {R : A ⥤ B} {V : D ⥤ B} (b : L ⋙ V ≅ T ⋙ R)
    (M : Endofunctor.IsoAlgebra F) :
    (Functor.isoHComp (Endofunctor.IsoAlgebra.mapOfNatIsoCompForgetIso e).symm b.symm).hom.app M =
      b.inv.app M.carrier :=
  Endofunctor.IsoAlgebra.isoHComp_forget_symm_hom_app e b.symm M

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

/-- Rotate the comparison using natural-transformation components throughout. -/
lemma tensorSquare_rotate_components
    {C D E H : Type*} [Category C] [Category D] [Category E] [Category H]
    [MonoidalCategory E] [MonoidalCategory H]
    (P : C ⥤ D) (U : D ⥤ H) (V : C ⥤ E) (G : E ⥤ H)
    (TC : C × C ⥤ C) (TD : D × D ⥤ D)
    (mu : TC ⋙ P ≅ P.prod P ⋙ TD)
    (nY : TC ⋙ V ≅ V.prod V ⋙ Functor.uncurry.obj (curriedTensor E))
    (nZ : TD ⋙ U ≅ U.prod U ⋙ Functor.uncurry.obj (curriedTensor H))
    (a : V ⋙ G ≅ P ⋙ U) (M N : C)
    (d : G.obj (V.obj M ⊗ V.obj N) ⟶ G.obj (V.obj M) ⊗ G.obj (V.obj N))
    (h : G.map (nY.inv.app (M, N)) ≫ a.hom.app (TC.obj (M, N)) ≫
        U.map (mu.hom.app (M, N)) =
      d ≫ (a.hom.app M ⊗ₘ a.hom.app N) ≫ nZ.inv.app (P.obj M, P.obj N)) :
    U.map (mu.hom.app (M, N)) ≫ nZ.hom.app (P.obj M, P.obj N) ≫
        (a.inv.app M ⊗ₘ a.inv.app N) =
      a.inv.app (TC.obj (M, N)) ≫ G.map (nY.hom.app (M, N)) ≫ d :=
  tensorSquare_rotate (G.mapIso (nY.app (M, N))) (a.app (TC.obj (M, N)))
    (U.map (mu.hom.app (M, N))) (nZ.app (P.obj M, P.obj N)) (a.app M) (a.app N) d h

section SquarePredicates

variable {C D E H : Type*} [Category C] [Category D] [Category E] [Category H]
  [MonoidalCategory E] [MonoidalCategory H]
  (P : C ⥤ D) (U : D ⥤ H) (V : C ⥤ E) (G : E ⥤ H) [G.OplaxMonoidal]
  (TC : C × C ⥤ C) (TD : D × D ⥤ D)
  (mu : TC ⋙ P ≅ P.prod P ⋙ TD)
  (nY : TC ⋙ V ≅ V.prod V ⋙ Functor.uncurry.obj (curriedTensor E))
  (nZ : TD ⋙ U ≅ U.prod U ⋙ Functor.uncurry.obj (curriedTensor H))
  (a : V ⋙ G ≅ P ⋙ U) (M N : C)

/-- The pullback tensor square, with its object conversions checked abstractly. -/
def PullTensorSquare : Prop :=
  U.map (mu.hom.app (M, N)) ≫ nZ.hom.app (P.obj M, P.obj N) ≫
      (a.inv.app M ⊗ₘ a.inv.app N) =
    a.inv.app (TC.obj (M, N)) ≫ G.map (nY.hom.app (M, N)) ≫
      Functor.OplaxMonoidal.δ G (V.obj M) (V.obj N)

/-- The inverse orientation of the same square. -/
def PullTensorInverseSquare : Prop :=
  G.map (nY.inv.app (M, N)) ≫ a.hom.app (TC.obj (M, N)) ≫
      U.map (mu.hom.app (M, N)) =
    Functor.OplaxMonoidal.δ G (V.obj M) (V.obj N) ≫
      (a.hom.app M ⊗ₘ a.hom.app N) ≫ nZ.inv.app (P.obj M, P.obj N)

lemma PullTensorInverseSquare.rotate
    (h : PullTensorInverseSquare P U V G TC TD mu nY nZ a M N) :
    PullTensorSquare P U V G TC TD mu nY nZ a M N :=
  tensorSquare_rotate_components P U V G TC TD mu nY nZ a M N
    (Functor.OplaxMonoidal.δ G (V.obj M) (V.obj N)) h

end SquarePredicates

end CategoryTheory
