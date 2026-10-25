/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleMonoidalComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleMonoidalShift

/-!
# The tensor comparison of the bounded constructible pullback commutes with the shifts

The oplax structure map `δ : Lf^*(A ⊗ C) ⟶ Lf^* A ⊗ Lf^* C` of the derived pullback
`Lf^* : Dᵇc(Y)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧` commutes with the shifts in each variable
(`ProEtale.CondensedRing.commShift_boundedConstructibleUpperStarδFlip`,
`ProEtale.CondensedRing.commShift_boundedConstructibleUpperStarδ`). Through the inclusions, `δ`
is the tensor comparison of the ambient derived pullback, which commutes with the shifts
(`ProEtale.CondensedRing.commShift_leftDerivedUpperStarTensor_flipApp`,
`ProEtale.CondensedRing.commShift_leftDerivedUpperStarTensor_app`). The transport along the
inclusions is the general statement `ObjectProperty.commShift_of_lift_flip_app`
(resp. `ObjectProperty.commShift_of_lift_app`) about restrictions of functors to full monoidal
subcategories.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory.ObjectProperty

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  {P : ObjectProperty C} [P.IsMonoidal] {Q : ObjectProperty D} [Q.IsMonoidal]
  {A : Type*} [AddMonoid A] [HasShift C A] [HasShift D A] [P.IsStableUnderShift A]
  [Q.IsStableUnderShift A] (F : C ⥤ D) [F.CommShift A]
  (hF : ∀ X : P.FullSubcategory, Q (F.obj X.obj))

/-- Let `G = Q.lift (P.ι ⋙ F)` be the restriction of `F` to full monoidal subcategories. A natural
transformation `τ : (- ⊗ Y) ⋙ G ⟶ G ⋙ (- ⊗ G Y)` commutes with the shifts if its components are
those of a natural transformation `σ : (- ⊗ Y) ⋙ F ⟶ F ⋙ (- ⊗ F Y)` commuting with the shifts. -/
lemma commShift_of_lift_flip_app [∀ X : C, ((curriedTensor C).flip.obj X).CommShift A]
    [∀ X : D, ((curriedTensor D).flip.obj X).CommShift A] (Y : P.FullSubcategory)
    (τ : (curriedTensor P.FullSubcategory).flip.obj Y ⋙ Q.lift (P.ι ⋙ F) hF ⟶
      Q.lift (P.ι ⋙ F) hF ⋙
        (curriedTensor Q.FullSubcategory).flip.obj ((Q.lift (P.ι ⋙ F) hF).obj Y))
    (σ : (curriedTensor C).flip.obj Y.obj ⋙ F ⟶ F ⋙ (curriedTensor D).flip.obj (F.obj Y.obj))
    [NatTrans.CommShift σ A] (h : ∀ X, (τ.app X).hom = σ.app X.obj) :
    NatTrans.CommShift τ A := by
  have : Q.ι.Faithful := Q.faithful_ι
  let e₁ : ((curriedTensor P.FullSubcategory).flip.obj Y ⋙ Q.lift (P.ι ⋙ F) hF) ⋙ Q.ι ≅
      P.ι ⋙ ((curriedTensor C).flip.obj Y.obj ⋙ F) :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (Q.liftCompιIso _ hF) ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (P.tensorRightCompιIso Y) _ ≪≫
      Functor.associator _ _ _
  let e₂ : (Q.lift (P.ι ⋙ F) hF ⋙ (curriedTensor Q.FullSubcategory).flip.obj
      ((Q.lift (P.ι ⋙ F) hF).obj Y)) ⋙ Q.ι ≅
      P.ι ⋙ (F ⋙ (curriedTensor D).flip.obj (F.obj Y.obj)) :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (Q.tensorRightCompιIso _) ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (Q.liftCompιIso _ hF) _ ≪≫
      Functor.associator _ _ _
  have : NatTrans.CommShift e₁.hom A := by
    dsimp only [e₁, Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Iso.symm_hom]
    infer_instance
  have : NatTrans.CommShift e₂.hom A := by
    dsimp only [e₂, Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Iso.symm_hom]
    infer_instance
  refine NatTrans.CommShift.of_whiskerRight_eq _ Q.ι e₁ e₂ (Functor.whiskerLeft P.ι σ) ?_
  ext X
  simp only [e₁, e₂, Iso.trans_hom, Iso.trans_inv, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app, liftCompιIso,
    tensorRightCompιIso, tensorRightIsoLift, liftFullSubcategoryCompιIso, Iso.refl_hom,
    Iso.refl_inv, NatTrans.id_app, NatIso.ofComponents_inv_app, ι_map, h, Category.id_comp,
    Category.comp_id, FullSubcategory.id_hom, NatIso.ofComponents_hom_app, Functor.flip_obj_map,
    Functor.comp_obj, ι_obj, lift_obj_obj, Functor.flip_obj_obj, curriedTensor_obj_obj,
    CategoryTheory.Functor.map_id]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

/-- Let `G = Q.lift (P.ι ⋙ F)` be the restriction of `F` to full monoidal subcategories. A natural
transformation `τ : (Y ⊗ -) ⋙ G ⟶ G ⋙ (G Y ⊗ -)` commutes with the shifts if its components are
those of a natural transformation `σ : (Y ⊗ -) ⋙ F ⟶ F ⋙ (F Y ⊗ -)` commuting with the shifts. -/
lemma commShift_of_lift_app [∀ X : C, ((curriedTensor C).obj X).CommShift A]
    [∀ X : D, ((curriedTensor D).obj X).CommShift A] (Y : P.FullSubcategory)
    (τ : (curriedTensor P.FullSubcategory).obj Y ⋙ Q.lift (P.ι ⋙ F) hF ⟶
      Q.lift (P.ι ⋙ F) hF ⋙
        (curriedTensor Q.FullSubcategory).obj ((Q.lift (P.ι ⋙ F) hF).obj Y))
    (σ : (curriedTensor C).obj Y.obj ⋙ F ⟶ F ⋙ (curriedTensor D).obj (F.obj Y.obj))
    [NatTrans.CommShift σ A] (h : ∀ X, (τ.app X).hom = σ.app X.obj) :
    NatTrans.CommShift τ A := by
  have : Q.ι.Faithful := Q.faithful_ι
  let e₁ : ((curriedTensor P.FullSubcategory).obj Y ⋙ Q.lift (P.ι ⋙ F) hF) ⋙ Q.ι ≅
      P.ι ⋙ ((curriedTensor C).obj Y.obj ⋙ F) :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (Q.liftCompιIso _ hF) ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (P.tensorLeftCompιIso Y) _ ≪≫
      Functor.associator _ _ _
  let e₂ : (Q.lift (P.ι ⋙ F) hF ⋙ (curriedTensor Q.FullSubcategory).obj
      ((Q.lift (P.ι ⋙ F) hF).obj Y)) ⋙ Q.ι ≅
      P.ι ⋙ (F ⋙ (curriedTensor D).obj (F.obj Y.obj)) :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (Q.tensorLeftCompιIso _) ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (Q.liftCompιIso _ hF) _ ≪≫
      Functor.associator _ _ _
  have : NatTrans.CommShift e₁.hom A := by
    dsimp only [e₁, Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Iso.symm_hom]
    infer_instance
  have : NatTrans.CommShift e₂.hom A := by
    dsimp only [e₂, Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Iso.symm_hom]
    infer_instance
  refine NatTrans.CommShift.of_whiskerRight_eq _ Q.ι e₁ e₂ (Functor.whiskerLeft P.ι σ) ?_
  ext X
  simp only [e₁, e₂, Iso.trans_hom, Iso.trans_inv, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app, liftCompιIso,
    tensorLeftCompιIso, tensorLeftIsoLift, liftFullSubcategoryCompιIso, Iso.refl_hom,
    Iso.refl_inv, NatTrans.id_app, NatIso.ofComponents_inv_app, ι_map, h, Category.id_comp,
    Category.comp_id, FullSubcategory.id_hom, NatIso.ofComponents_hom_app, curriedTensor_obj_map,
    Functor.comp_obj, ι_obj, lift_obj_obj, curriedTensor_obj_obj, MonoidalCategory.whiskerLeft_id]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

end CategoryTheory.ObjectProperty

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  [IsEllAdicFinitenessCoefficient ℓ Λ]
  {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

/-- The oplax structure map `Lf^*(A ⊗ C) ⟶ Lf^* A ⊗ Lf^* C` for fixed `C`, natural in `A`. -/
@[simps]
noncomputable def boundedConstructibleUpperStarδFlip (C : Dᵇc(Y.left)⟦Λ⟧) :
    (curriedTensor (Dᵇc(Y.left)⟦Λ⟧)).flip.obj C ⋙ boundedConstructibleUpperStar Λ ℓ f ⟶
      boundedConstructibleUpperStar Λ ℓ f ⋙
        (curriedTensor (Dᵇc(X.left)⟦Λ⟧)).flip.obj
          ((boundedConstructibleUpperStar Λ ℓ f).obj C) where
  app A := Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar Λ ℓ f) A C
  naturality _ _ g := by
    dsimp
    exact (Functor.OplaxMonoidal.δ_natural_left (boundedConstructibleUpperStar Λ ℓ f) g C).symm

/-- The oplax structure map `Lf^*(C ⊗ A) ⟶ Lf^* C ⊗ Lf^* A` for fixed `C`, natural in `A`. -/
@[simps]
noncomputable def boundedConstructibleUpperStarδ (C : Dᵇc(Y.left)⟦Λ⟧) :
    (curriedTensor (Dᵇc(Y.left)⟦Λ⟧)).obj C ⋙ boundedConstructibleUpperStar Λ ℓ f ⟶
      boundedConstructibleUpperStar Λ ℓ f ⋙
        (curriedTensor (Dᵇc(X.left)⟦Λ⟧)).obj ((boundedConstructibleUpperStar Λ ℓ f).obj C) where
  app A := Functor.OplaxMonoidal.δ (boundedConstructibleUpperStar Λ ℓ f) C A
  naturality _ _ g := by
    dsimp
    exact (Functor.OplaxMonoidal.δ_natural_right (boundedConstructibleUpperStar Λ ℓ f) C g).symm

/-- The oplax structure map `Lf^*(A ⊗ C) ⟶ Lf^* A ⊗ Lf^* C` of the derived pullback on bounded
constructible complexes commutes with the shifts in `A`. -/
instance commShift_boundedConstructibleUpperStarδFlip (C : Dᵇc(Y.left)⟦Λ⟧) :
    NatTrans.CommShift (boundedConstructibleUpperStarδFlip Λ ℓ f C) ℤ := by
  let := commShiftTensorRightFamily Λ X.left
  let := commShiftTensorRightFamily Λ Y.left
  exact ObjectProperty.commShift_of_lift_flip_app L((f.left)^*⟦Λ⟧) _ C _
    (Adjunction.comparisonFlipApp (leftDerivedUpperStarTensor Λ f.left) C.obj)
    (fun A ↦ δ_boundedConstructibleUpperStar_hom Λ ℓ f A C)

/-- The oplax structure map `Lf^*(C ⊗ A) ⟶ Lf^* C ⊗ Lf^* A` of the derived pullback on bounded
constructible complexes commutes with the shifts in `A`. -/
instance commShift_boundedConstructibleUpperStarδ (C : Dᵇc(Y.left)⟦Λ⟧) :
    NatTrans.CommShift (boundedConstructibleUpperStarδ Λ ℓ f C) ℤ := by
  let := commShiftTensorLeftFamily Λ X.left
  let := commShiftTensorLeftFamily Λ Y.left
  exact ObjectProperty.commShift_of_lift_app L((f.left)^*⟦Λ⟧) _ C _
    ((leftDerivedUpperStarTensor Λ f.left).app C.obj)
    (fun A ↦ δ_boundedConstructibleUpperStar_hom Λ ℓ f C A)

end AlgebraicGeometry.ProEtale.CondensedRing
