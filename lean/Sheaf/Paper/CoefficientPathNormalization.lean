/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CoefficientScalarTensorRealization
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryCounit

/-! # Normalization of the left-derived coefficient path

Source: Stacks Project, Tags 0D6D and 0D6E; blueprint rational proper base change (3).
(blueprint: lem-sfb-coefficient-left-derived-path-normalization).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Obj

universe u

private theorem localized_conjugate
    {A B DA DB : Type*} [Category A] [Category B] [Category DA] [Category DB]
    {L₁ L₂ : A ⥤ B} {R₁ R₂ : B ⥤ A}
    {LD₁ LD₂ : DA ⥤ DB} {RD₁ RD₂ : DB ⥤ DA}
    (Q : A ⥤ DA) (Q' : B ⥤ DB) (W : MorphismProperty A) [Q.IsLocalization W]
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (ad₁ : LD₁ ⊣ RD₁) (ad₂ : LD₂ ⊣ RD₂)
    (α₁ : Q ⋙ LD₁ ≅ L₁ ⋙ Q') (α₂ : Q ⋙ LD₂ ≅ L₂ ⋙ Q')
    (β₁ : R₁ ⋙ Q ⟶ Q' ⋙ RD₁) (β₂ : R₂ ⋙ Q ⟶ Q' ⋙ RD₂)
    (h₁ : ∀ P, ad₁.unit.app (Q.obj P) ≫ RD₁.map (α₁.hom.app P) =
      Q.map (a₁.unit.app P) ≫ β₁.app (L₁.obj P))
    (h₂ : ∀ P, ad₂.unit.app (Q.obj P) ≫ RD₂.map (α₂.hom.app P) =
      Q.map (a₂.unit.app P) ≫ β₂.app (L₂.obj P))
    (e : L₂ ≅ L₁) (d : R₁ ≅ R₂)
    (he : d.hom = conjugateEquiv a₁ a₂ e.hom)
    (eD : LD₂ ≅ LD₁) (dD : RD₁ ≅ RD₂)
    (hα : ∀ P, eD.hom.app (Q.obj P) ≫ α₁.hom.app P =
      α₂.hom.app P ≫ Q'.map (e.hom.app P))
    (hβ : ∀ K, β₁.app K ≫ dD.hom.app (Q'.obj K) =
      Q.map (d.hom.app K) ≫ β₂.app K) :
    eD.hom = (conjugateEquiv ad₁ ad₂).symm dD.hom := by
  apply Localization.natTrans_ext Q W
  intro P
  have hu : ad₁.unit.app (Q.obj P) ≫ dD.hom.app (LD₁.obj (Q.obj P)) =
      ad₂.unit.app (Q.obj P) ≫ RD₂.map (eD.hom.app (Q.obj P)) := by
    apply (cancel_mono (RD₂.map (α₁.hom.app P))).1
    rw [Category.assoc, ← dD.hom.naturality, ← Category.assoc, h₁,
      Category.assoc]
    erw [hβ]
    rw [← Q.map_comp_assoc, he, unit_conjugateEquiv,
      Q.map_comp, Category.assoc]
    erw [β₂.naturality]
    rw [← Category.assoc, ← h₂]
    simp only [Functor.comp_map, Category.assoc, ← RD₂.map_comp]
    rw [hα]
  apply (ad₂.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  rw [← hu, ← unit_conjugateEquiv_symm ad₁ ad₂ dD.hom]

private theorem transport_normalization
    {A B DA DB : Type*} [Category A] [Category B] [Category DA] [Category DB]
    {L : A ⥤ B} {R : B ⥤ A} {LD : DA ⥤ DB} {RD RD' : DB ⥤ DA}
    {Q : A ⥤ DA} {Q' : B ⥤ DB} (ad : LD ⊣ RD) (i : RD ≅ RD')
    (α : Q ⋙ LD ⟶ L ⋙ Q') (β : R ⋙ Q ⟶ Q' ⋙ RD)
    (β' : R ⋙ Q ⟶ Q' ⋙ RD') (η : 𝟭 A ⟶ L ⋙ R)
    (hβ : β ≫ Functor.whiskerLeft Q' i.hom = β')
    (h : ∀ P, ad.unit.app (Q.obj P) ≫ RD.map (α.app P) =
      Q.map (η.app P) ≫ β.app (L.obj P)) (P : A) :
    (ad.ofNatIsoRight i).unit.app (Q.obj P) ≫ RD'.map (α.app P) =
      Q.map (η.app P) ≫ β'.app (L.obj P) := by
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [Category.assoc, ← i.hom.naturality, ← Category.assoc, h, Category.assoc]
  exact congrArg (fun t ↦ Q.map (η.app P) ≫ t) (NatTrans.congr_app hβ (L.obj P))

private theorem inverse_square
    {C : Type*} [Category C] {A B D E : C}
    (p : A ⟶ B) (q : D ⟶ E) (d : B ≅ E) (e : A ≅ D)
    (h : q ≫ d.inv = e.inv ≫ p) : p ≫ d.hom = e.hom ≫ q := by
  apply (cancel_mono d.inv).1
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [h, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

private theorem iso_path_normalization
    {C : Type*} [Category C] {A B D E Y Z : C}
    (i : A ≅ B) (j : D ≅ E) (n : D ≅ A)
    (α : B ⟶ Z) (β : E ⟶ Y) (ε : A ⟶ Z) (δ : D ⟶ Y) (q : Y ⟶ Z)
    (hi : i.hom ≫ α = ε) (hj : j.hom ≫ β = δ) (hn : n.hom ≫ ε = δ ≫ q) :
    (j.symm ≪≫ n ≪≫ i).hom ≫ α = β ≫ q := by
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [hi, hn, ← hj, Category.assoc, Iso.inv_hom_id_assoc]

private def compLeft
    {A B C DA DB DC : Type*}
    [Category A] [Category B] [Category C] [Category DA] [Category DB] [Category DC]
    {F : A ⥤ B} {G : B ⥤ C} {FD : DA ⥤ DB} {GD : DB ⥤ DC}
    {QA : A ⥤ DA} {QB : B ⥤ DB} {QC : C ⥤ DC}
    (α : QA ⋙ FD ≅ F ⋙ QB) (γ : QB ⋙ GD ≅ G ⋙ QC) :
    QA ⋙ (FD ⋙ GD) ≅ (F ⋙ G) ⋙ QC :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight α GD ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft F γ ≪≫
    (Functor.associator _ _ _).symm

private def compRight
    {A B C DA DB DC : Type*}
    [Category A] [Category B] [Category C] [Category DA] [Category DB] [Category DC]
    {R : B ⥤ A} {S : C ⥤ B} {RD : DB ⥤ DA} {SD : DC ⥤ DB}
    {QA : A ⥤ DA} {QB : B ⥤ DB} {QC : C ⥤ DC}
    (β : R ⋙ QA ⟶ QB ⋙ RD) (δ : S ⋙ QB ⟶ QC ⋙ SD) :
    (S ⋙ R) ⋙ QA ⟶ QC ⋙ (SD ⋙ RD) :=
  (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft S β ≫
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight δ RD ≫
    (Functor.associator _ _ _).hom

private theorem compLeft_hom_app
    {A B C DA DB DC : Type*}
    [Category A] [Category B] [Category C] [Category DA] [Category DB] [Category DC]
    {F : A ⥤ B} {G : B ⥤ C} {FD : DA ⥤ DB} {GD : DB ⥤ DC}
    {QA : A ⥤ DA} {QB : B ⥤ DB} {QC : C ⥤ DC}
    (α : QA ⋙ FD ≅ F ⋙ QB) (γ : QB ⋙ GD ≅ G ⋙ QC) (P : A) :
    (compLeft α γ).hom.app P = GD.map (α.hom.app P) ≫ γ.hom.app (F.obj P) := by
  simp [compLeft]

private theorem compRight_app
    {A B C DA DB DC : Type*}
    [Category A] [Category B] [Category C] [Category DA] [Category DB] [Category DC]
    {R : B ⥤ A} {S : C ⥤ B} {RD : DB ⥤ DA} {SD : DC ⥤ DB}
    {QA : A ⥤ DA} {QB : B ⥤ DB} {QC : C ⥤ DC}
    (β : R ⋙ QA ⟶ QB ⋙ RD) (δ : S ⋙ QB ⟶ QC ⋙ SD) (P : C) :
    (compRight β δ).app P = β.app (S.obj P) ≫ RD.map (δ.app P) := by
  simp [compRight]

private theorem comp_normalization
    {A B C DA DB DC : Type*}
    [Category A] [Category B] [Category C] [Category DA] [Category DB] [Category DC]
    {F : A ⥤ B} {G : B ⥤ C} {R : B ⥤ A} {S : C ⥤ B}
    {FD : DA ⥤ DB} {GD : DB ⥤ DC} {RD : DB ⥤ DA} {SD : DC ⥤ DB}
    {QA : A ⥤ DA} {QB : B ⥤ DB} {QC : C ⥤ DC}
    (a : F ⊣ R) (b : G ⊣ S) (ad : FD ⊣ RD) (bd : GD ⊣ SD)
    (α : QA ⋙ FD ≅ F ⋙ QB) (γ : QB ⋙ GD ≅ G ⋙ QC)
    (β : R ⋙ QA ⟶ QB ⋙ RD) (δ : S ⋙ QB ⟶ QC ⋙ SD)
    (hF : ∀ P, ad.unit.app (QA.obj P) ≫ RD.map (α.hom.app P) =
      QA.map (a.unit.app P) ≫ β.app (F.obj P))
    (hG : ∀ P, bd.unit.app (QB.obj P) ≫ SD.map (γ.hom.app P) =
      QB.map (b.unit.app P) ≫ δ.app (G.obj P)) (P : A) :
    (ad.comp bd).unit.app (QA.obj P) ≫
        (SD ⋙ RD).map ((compLeft α γ).hom.app P) =
      QA.map ((a.comp b).unit.app P) ≫ (compRight β δ).app ((F ⋙ G).obj P) := by
  simp only [compLeft, compRight, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.id_comp, Category.comp_id, Functor.comp_map, Functor.comp_obj,
    Adjunction.comp_unit_app, Functor.map_comp, Category.assoc]
  have hn := bd.unit.naturality (α.hom.app P)
  change α.hom.app P ≫ bd.unit.app (QB.obj (F.obj P)) =
    bd.unit.app (FD.obj (QA.obj P)) ≫ SD.map (GD.map (α.hom.app P)) at hn
  rw [← RD.map_comp_assoc, ← hn, RD.map_comp_assoc,
    ← Category.assoc, hF, Category.assoc, ← RD.map_comp, hG, RD.map_comp]
  erw [← β.naturality_assoc]
  rfl

private def homotopyIso
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    {F G : A ⥤ B} [F.Additive] [G.Additive] (e : F ≅ G) :
    F.mapHomotopyCategory (.up ℤ) ≅ G.mapHomotopyCategory (.up ℤ) where
  hom := NatTrans.mapHomotopyCategory e.hom (.up ℤ)
  inv := NatTrans.mapHomotopyCategory e.inv (.up ℤ)
  hom_inv_id := by rw [← NatTrans.mapHomotopyCategory_comp, e.hom_inv_id,
    NatTrans.mapHomotopyCategory_id]
  inv_hom_id := by rw [← NatTrans.mapHomotopyCategory_comp, e.inv_hom_id,
    NatTrans.mapHomotopyCategory_id]

private theorem homotopy_comp_inv
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Preadditive A] [Preadditive B] [Preadditive C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    (P : HomotopyCategory A (.up ℤ)) :
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app P = 𝟙 _ := by
  rw [← cancel_epi ((Functor.mapHomotopyCategoryCompIso
    (Iso.refl (F ⋙ G)) (.up ℤ)).hom.app P), Iso.hom_inv_id_app,
    Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.comp_id]

private theorem homotopy_comp_map
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Preadditive A] [Preadditive B] [Preadditive C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    {P P' : HomotopyCategory A (.up ℤ)} (t : P ⟶ P') :
    (G.mapHomotopyCategory (.up ℤ)).map
      ((F.mapHomotopyCategory (.up ℤ)).map t) =
        ((F ⋙ G).mapHomotopyCategory (.up ℤ)).map t := by
  have h := (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).hom.naturality t
  simpa only [Functor.mapHomotopyCategoryCompIso_refl_hom_app,
    Functor.comp_map, Category.id_comp, Category.comp_id] using h

private theorem homotopy_comp_unit
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Preadditive A] [Preadditive B] [Preadditive C]
    [HasBinaryBiproducts A] [HasBinaryBiproducts B] [HasBinaryBiproducts C]
    {F : A ⥤ B} {G : B ⥤ C} {U : B ⥤ A} {V : C ⥤ B}
    [F.Additive] [G.Additive] [U.Additive] [V.Additive]
    (a : F ⊣ U) (b : G ⊣ V) (P : HomotopyCategory A (.up ℤ)) :
    ((a.mapHomotopyCategory (.up ℤ)).comp (b.mapHomotopyCategory (.up ℤ))).unit.app P =
      ((a.comp b).mapHomotopyCategory (.up ℤ)).unit.app P := by
  have h := Adjunction.mapHomotopyCategory_comp_unit_app (.up ℤ) a b P
  rw [Functor.mapHomotopyCategoryCompIso_refl_hom_app,
    Functor.mapHomotopyCategoryCompIso_refl_hom_app] at h
  erw [CategoryTheory.Functor.map_id, Category.comp_id, Category.comp_id] at h
  simpa only [Adjunction.comp_unit_app] using h.symm

private def homotopySquare
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Preadditive A] [Preadditive B] [Preadditive C] [Preadditive D]
    {F : A ⥤ B} {E : B ⥤ D} {G : A ⥤ C} {H : C ⥤ D}
    [F.Additive] [E.Additive] [G.Additive] [H.Additive]
    (e : G ⋙ H ≅ F ⋙ E) :
    G.mapHomotopyCategory (.up ℤ) ⋙ H.mapHomotopyCategory (.up ℤ) ≅
      F.mapHomotopyCategory (.up ℤ) ⋙ E.mapHomotopyCategory (.up ℤ) :=
  Functor.mapHomotopyCategoryCompIso (Iso.refl (G ⋙ H)) (.up ℤ) ≪≫
    homotopyIso e ≪≫ (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (F ⋙ E)) (.up ℤ)).symm

private theorem homotopySquare_hom
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Preadditive A] [Preadditive B] [Preadditive C] [Preadditive D]
    {F : A ⥤ B} {E : B ⥤ D} {G : A ⥤ C} {H : C ⥤ D}
    [F.Additive] [E.Additive] [G.Additive] [H.Additive]
    (e : G ⋙ H ≅ F ⋙ E) (P : HomotopyCategory A (.up ℤ)) :
    (homotopySquare e).hom.app P =
      (NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app P := by
  simp only [homotopySquare, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.mapHomotopyCategoryCompIso_refl_hom_app, homotopy_comp_inv,
    Category.id_comp, Category.comp_id, homotopyIso]

private theorem homotopySquare_conjugate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Preadditive A] [Preadditive B] [Preadditive C] [Preadditive D]
    [HasBinaryBiproducts A] [HasBinaryBiproducts B]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    {F : A ⥤ B} {E : B ⥤ D} {G : A ⥤ C} {H : C ⥤ D}
    {U : B ⥤ A} {V : D ⥤ B} {W : C ⥤ A} {T : D ⥤ C}
    [F.Additive] [E.Additive] [G.Additive] [H.Additive]
    [U.Additive] [V.Additive] [W.Additive] [T.Additive]
    (ar : F ⊣ U) (ax : E ⊣ V) (ay : G ⊣ W) (as' : H ⊣ T)
    (e : G ⋙ H ≅ F ⋙ E) (d : V ⋙ U ≅ T ⋙ W)
    (he : d.hom = conjugateEquiv (ar.comp ax) (ay.comp as') e.hom) :
    (homotopySquare d).hom = conjugateEquiv
      ((ar.mapHomotopyCategory (.up ℤ)).comp (ax.mapHomotopyCategory (.up ℤ)))
      ((ay.mapHomotopyCategory (.up ℤ)).comp (as'.mapHomotopyCategory (.up ℤ)))
      (homotopySquare e).hom := by
  symm
  apply conjugateEquiv_eq_of_unit
  intro P
  rw [homotopySquare_hom, homotopySquare_hom, homotopy_comp_unit, homotopy_comp_unit,
    Functor.comp_map, homotopy_comp_map]
  exact (Adjunction.mapHomotopyCategory_unit_app_comp (.up ℤ)
    (ay.comp as') (ar.comp ax) e.hom d.hom
    (fun M ↦ (he ▸ unit_conjugateEquiv (ar.comp ax) (ay.comp as') e.hom M).symm) P).symm

private theorem left_square_normalization
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [MonoidalCategory A] [MonoidalPreadditive A]
    [HasCountableCoproducts A]
    [HasColimitsOfShape ℤ A] [HasExactColimitsOfShape ℤ A]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [∀ (X : A), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor A).obj X)]
    [∀ (X : A), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor A).flip.obj X)]
    [Abelian.HasFunctorialFlatResolution A]
    [MonoidalCategory B] [MonoidalPreadditive B]
    [HasCountableCoproducts B]
    [HasColimitsOfShape ℤ B] [HasExactColimitsOfShape ℤ B]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ B), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ B), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ B), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [∀ (X : B), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor B).obj X)]
    [∀ (X : B), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor B).flip.obj X)]
    [Abelian.HasFunctorialFlatResolution B]
    [MonoidalCategory C] [MonoidalPreadditive C]
    [HasCountableCoproducts C]
    [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [∀ (X : C), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor C).obj X)]
    [∀ (X : C), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor C).flip.obj X)]
    [Abelian.HasFunctorialFlatResolution C]
    (F : A ⥤ B) (E : B ⥤ D) (G : A ⥤ C) (H : C ⥤ D)
    [F.Additive] [E.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : G ⋙ H ≅ F ⋙ E) (P : HomotopyCategory A (.up ℤ)) :
    ((G.leftDerivedFunctorCompIso H).symm ≪≫ (G ⋙ H).leftDerivedFunctorNatIso e ≪≫
        F.leftDerivedFunctorCompIso E).hom.app (DerivedCategory.Qh.obj P) ≫
        (compLeft (asIso F.leftDerivedFunctorCounit)
          (asIso E.leftDerivedFunctorCounit)).hom.app P =
      (compLeft (asIso G.leftDerivedFunctorCounit)
        (asIso H.leftDerivedFunctorCounit)).hom.app P ≫
          DerivedCategory.Qh.map ((homotopySquare e).hom.app P) := by
  have h1 := F.leftDerivedFunctorCompIso_hom_app_Qh E P
  have h2 := G.leftDerivedFunctorCompIso_hom_app_Qh H P
  have h3 := (G ⋙ H).leftDerivedFunctorNatIso_hom_app_Qh e P
  simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Iso.app_hom,
    Iso.app_inv] using iso_path_normalization
      ((F.leftDerivedFunctorCompIso E).app (DerivedCategory.Qh.obj P))
      ((G.leftDerivedFunctorCompIso H).app (DerivedCategory.Qh.obj P))
      (((G ⋙ H).leftDerivedFunctorNatIso e).app (DerivedCategory.Qh.obj P))
      ((compLeft (asIso F.leftDerivedFunctorCounit)
        (asIso E.leftDerivedFunctorCounit)).hom.app P)
      ((compLeft (asIso G.leftDerivedFunctorCounit)
        (asIso H.leftDerivedFunctorCounit)).hom.app P)
      ((F ⋙ E).leftDerivedFunctorCounit.app P)
      ((G ⋙ H).leftDerivedFunctorCounit.app P)
      (DerivedCategory.Qh.map ((homotopySquare e).hom.app P))
      (by simpa only [compLeft_hom_app, asIso_hom, Iso.app_hom, Functor.comp_obj] using h1)
      (by simpa only [compLeft_hom_app, asIso_hom, Iso.app_hom, Functor.comp_obj] using h2)
      (by simpa only [homotopySquare_hom, Iso.app_hom, Functor.comp_obj] using h3)

private theorem right_square_normalization
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions B]
    [Abelian.HasKInjectiveResolutions C]
    (V : A ⥤ B) (U : B ⥤ D) (T : A ⥤ C) (W : C ⥤ D)
    [V.Additive] [U.Additive] [T.Additive] [W.Additive]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits W] [PreservesFiniteColimits W]
    [V.PreservesKInjectiveComplexes] (e : T ⋙ W ≅ V ⋙ U)
    (K : HomotopyCategory A (.up ℤ)) :
    (compRight W.mapDerivedCategoryFactorsh.inv T.rightDerivedFunctorUnit).app K ≫
        ((Functor.rightDerivedFunctorCompMapDerivedCategoryIso T W).symm ≪≫
          Functor.rightDerivedFunctorNatIso e ≪≫ Functor.rightDerivedFunctorCompIso V U ≪≫
          Functor.isoWhiskerRight V.rightDerivedFunctorIsoMapDerivedCategory
            U.rightDerivedFunctor).hom.app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((homotopySquare e.symm).inv.app K) ≫
        (compRight U.rightDerivedFunctorUnit V.mapDerivedCategoryFactorsh.inv).app K := by
  have hcT : (Functor.rightDerivedFunctorCompMapDerivedCategoryUnit T W).app K =
      DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
    (Iso.refl (T ⋙ W)) (.up ℤ)).inv.app K) ≫
      (compRight W.mapDerivedCategoryFactorsh.inv T.rightDerivedFunctorUnit).app K := by
    simp only [Functor.rightDerivedFunctorCompMapDerivedCategoryUnit, compRight_app,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id]
  have h1 : (Functor.rightDerivedFunctorCompMapDerivedCategoryUnit T W).app K ≫
      (Functor.rightDerivedFunctorCompMapDerivedCategoryIso T W).inv.app
    (DerivedCategory.Qh.obj K) = (T ⋙ W).rightDerivedFunctorUnit.app K := by
    simp [Functor.rightDerivedFunctorCompMapDerivedCategoryIso]
  have h2 : (T ⋙ W).rightDerivedFunctorUnit.app K ≫
      (Functor.rightDerivedFunctorNatIso e).hom.app
    (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map
      ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app K) ≫
    (V ⋙ U).rightDerivedFunctorUnit.app K := by
    simpa only [Functor.rightDerivedFunctorNatIso,
      Functor.rightDerivedFunctorNatTrans, Functor.whiskerRight_app] using
      Functor.rightDerivedNatTrans_app
        (T ⋙ W).rightDerivedFunctor (V ⋙ U).rightDerivedFunctor
        (T ⋙ W).rightDerivedFunctorUnit (V ⋙ U).rightDerivedFunctorUnit
        (HomotopyCategory.quasiIso _ (.up ℤ))
        (Functor.whiskerRight
          (NatTrans.mapHomotopyCategory e.hom (.up ℤ)) DerivedCategory.Qh) K
  have h3 : (V ⋙ U).rightDerivedFunctorUnit.app K ≫
      (Functor.rightDerivedFunctorCompIso V U).hom.app (DerivedCategory.Qh.obj K) =
      (Functor.rightDerivedFunctorCompUnit V U).app K := by
    simp [Functor.rightDerivedFunctorCompIso]
  have h4 : (Functor.rightDerivedFunctorCompUnit V U).app K ≫
      (Functor.isoWhiskerRight V.rightDerivedFunctorIsoMapDerivedCategory
    U.rightDerivedFunctor).hom.app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
    (Iso.refl (V ⋙ U)) (.up ℤ)).inv.app K) ≫
      (compRight U.rightDerivedFunctorUnit V.mapDerivedCategoryFactorsh.inv).app K := by
    simp only [Functor.rightDerivedFunctorCompUnit, compRight_app,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.isoWhiskerRight_hom, Functor.associator_hom_app,
      Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, Category.assoc]
    rw [← U.rightDerivedFunctor.map_comp]
    have hf := NatTrans.congr_app V.rightDerivedFunctorIsoMapDerivedCategory_hom_fac K
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hf
    erw [hf]
  apply (cancel_epi (DerivedCategory.Qh.map
    ((Functor.mapHomotopyCategoryCompIso (Iso.refl (T ⋙ W)) (.up ℤ)).inv.app K))).1
  rw [← Category.assoc, ← hcT]
  simp only [Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app]
  rw [reassoc_of% h1, reassoc_of% h2, reassoc_of% h3, h4]
  simp only [homotopySquare, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, homotopyIso, Category.assoc, Functor.map_comp]
  simp only [← DerivedCategory.Qh.map_comp_assoc, Iso.inv_hom_id_app_assoc]


namespace AlgebraicGeometry.ProEtale.CondensedRing

-- Compare the specified functors without expanding their derived models.
attribute [local irreducible] DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Sheaf.monoidalCategory CategoryTheory.Mod.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory upperStarFromPoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor derivedPullIso
  coefficientScalarPathIso internalScalarMonoidal upperStar lowerStar
  Functor.leftDerivedFunctorCounit Functor.rightDerivedFunctorUnit
  Functor.leftDerivedFunctorCompIso Functor.leftDerivedFunctorNatIso
  Functor.mapHomotopyCategory Functor.mapDerivedCategory
  Functor.mapDerivedCategoryFactorsh
  Mod.extendScalars Mod.comap

set_option maxHeartbeats 200000 in
-- Several specified derived adjunctions and their exact scalar transports are compared.
/-- The left-derived ordinary coefficient square is the inverse specified pull comparison.
Source: Stacks 0D6D, 0D6E; blueprint rational proper base change, proof (3).
(blueprint: lem-sfb-coefficient-left-derived-path-normalization).

Proof: Each left-derived comparison satisfies its counit factorization on the
homotopy category. The derived adjunction unit satisfies `derivedη_fac_app`;
transporting the scalar right adjoints along their exact-factorization isomorphisms
preserves this equation. Naturality pastes these equations for composite adjunctions.
The ordinary inverse pull square is conjugate to the inverse restriction square,
and this unit equation passes to homotopy categories. The defining right-derived
composition and natural-isomorphism comparisons, followed by exact scalar transport,
satisfy the corresponding right-unit equation. These left and right equations imply
the conjugation unit equation after localization. Localization detects equality of
natural transformations, and the derived adjunction Hom bijection detects equality
of components. The resulting inverse conjugate is precisely inverse derivedPullIso. -/
theorem coefficientScalarPathIso_eq_derivedPullIso_symm
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a]
    [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    coefficientScalarPathIso a f = (derivedPullIso a f).symm := by
  let F := upperStar R f
  let E := Mod.extendScalars (coefficientMap a X)
  let G := Mod.extendScalars (coefficientMap a Y)
  let H := upperStar S f
  let U := (lowerStar R f :
    ModuleRingedComparison.internalModules R X ⥤ ModuleRingedComparison.internalModules R Y)
  let V := (Mod.comap (coefficientMap a X) :
    ModuleRingedComparison.internalModules S X ⥤ ModuleRingedComparison.internalModules R X)
  let W := (Mod.comap (coefficientMap a Y) :
    ModuleRingedComparison.internalModules S Y ⥤ ModuleRingedComparison.internalModules R Y)
  let T := (lowerStar S f :
    ModuleRingedComparison.internalModules S X ⥤ ModuleRingedComparison.internalModules S Y)
  let ax := Mod.extendRestrictAdjunction (coefficientMap a X)
  let ay := Mod.extendRestrictAdjunction (coefficientMap a Y)
  let ar := upperStarLowerStarAdjunction R f
  let as' := upperStarLowerStarAdjunction S f
  let dx := Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X)
  let dy := Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y)
  let dr := derivedUpperStarLowerStarAdjunction R f
  let ds := derivedUpperStarLowerStarAdjunction S f
  let αF := @asIso _ _ _ _ F.leftDerivedFunctorCounit
    (Functor.isIso_leftDerivedFunctorCounit F)
  let αE := @asIso _ _ _ _ E.leftDerivedFunctorCounit
    (Functor.isIso_leftDerivedFunctorCounit E)
  let αG := @asIso _ _ _ _ G.leftDerivedFunctorCounit
    (Functor.isIso_leftDerivedFunctorCounit G)
  let αH := @asIso _ _ _ _ H.leftDerivedFunctorCounit
    (Functor.isIso_leftDerivedFunctorCounit H)
  let βU := U.rightDerivedFunctorUnit
  let βT := T.rightDerivedFunctorUnit
  have hF (P) : dr.unit.app (DerivedCategory.Qh.obj P) ≫
      U.rightDerivedFunctor.map (αF.hom.app P) =
      DerivedCategory.Qh.map ((ar.mapHomotopyCategory (.up ℤ)).unit.app P) ≫
        βU.app ((F.mapHomotopyCategory (.up ℤ)).obj P) :=
    (ar.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
      (HomotopyCategory.quasiIso _ (.up ℤ)) F.leftDerivedFunctorCounit U.rightDerivedFunctorUnit P
  have hH (P) : ds.unit.app (DerivedCategory.Qh.obj P) ≫
      T.rightDerivedFunctor.map (αH.hom.app P) =
      DerivedCategory.Qh.map ((as'.mapHomotopyCategory (.up ℤ)).unit.app P) ≫
        βT.app ((H.mapHomotopyCategory (.up ℤ)).obj P) :=
    (as'.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
      (HomotopyCategory.quasiIso _ (.up ℤ)) H.leftDerivedFunctorCounit T.rightDerivedFunctorUnit P
  have hE (P) : dx.unit.app (DerivedCategory.Qh.obj P) ≫
      V.mapDerivedCategory.map (αE.hom.app P) =
      DerivedCategory.Qh.map ((ax.mapHomotopyCategory (.up ℤ)).unit.app P) ≫
        V.mapDerivedCategoryFactorsh.inv.app ((E.mapHomotopyCategory (.up ℤ)).obj P) := by
    exact transport_normalization ax.derivedAdjunction
      V.rightDerivedFunctorIsoMapDerivedCategory αE.hom V.rightDerivedFunctorUnit
      V.mapDerivedCategoryFactorsh.inv (ax.mapHomotopyCategory (.up ℤ)).unit
      V.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
      ((ax.mapHomotopyCategory (.up ℤ)).derivedη_fac_app (HomotopyCategory.quasiIso _ (.up ℤ))
        E.leftDerivedFunctorCounit V.rightDerivedFunctorUnit) P
  have hG (P) : dy.unit.app (DerivedCategory.Qh.obj P) ≫
      W.mapDerivedCategory.map (αG.hom.app P) =
      DerivedCategory.Qh.map ((ay.mapHomotopyCategory (.up ℤ)).unit.app P) ≫
        W.mapDerivedCategoryFactorsh.inv.app ((G.mapHomotopyCategory (.up ℤ)).obj P) := by
    exact transport_normalization ay.derivedAdjunction
      W.rightDerivedFunctorIsoMapDerivedCategory αG.hom W.rightDerivedFunctorUnit
      W.mapDerivedCategoryFactorsh.inv (ay.mapHomotopyCategory (.up ℤ)).unit
      W.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
      ((ay.mapHomotopyCategory (.up ℤ)).derivedη_fac_app (HomotopyCategory.quasiIso _ (.up ℤ))
        G.leftDerivedFunctorCounit W.rightDerivedFunctorUnit) P
  let βV := V.mapDerivedCategoryFactorsh.inv
  let βW := W.mapDerivedCategoryFactorsh.inv
  let e := homotopySquare (pullIso a f).symm
  let d := homotopySquare (comapLowerStarIso a f).symm
  have he : d.hom = conjugateEquiv
      ((ar.mapHomotopyCategory (.up ℤ)).comp (ax.mapHomotopyCategory (.up ℤ)))
      ((ay.mapHomotopyCategory (.up ℤ)).comp (as'.mapHomotopyCategory (.up ℤ))) e.hom := by
    apply homotopySquare_conjugate ar ax ay as'
    have ho : conjugateIsoEquiv (ar.comp ax) (ay.comp as') (pullIso a f).symm =
        (comapLowerStarIso a f).symm := by
      change (conjugateIsoEquiv (ay.comp as') (ar.comp ax)
        ((conjugateIsoEquiv (ay.comp as') (ar.comp ax)).symm
          (comapLowerStarIso a f))).symm = _
      rw [Equiv.apply_symm_apply]
    exact (congrArg Iso.hom ho).symm
  have hα (P) : (coefficientScalarPathIso a f).hom.app (DerivedCategory.Qh.obj P) ≫
      (compLeft αF αE).hom.app P =
    (compLeft αG αH).hom.app P ≫ DerivedCategory.Qh.map (e.hom.app P) := by
    unfold coefficientScalarPathIso Functor.leftDerivedFunctorCompNatIso
    exact left_square_normalization F E G H (pullIso a f).symm P
  have hβ (K) : (compRight βU βV).app K ≫
      (derivedComapLowerStarIso a f).inv.app (DerivedCategory.Qh.obj K) =
    DerivedCategory.Qh.map (d.hom.app K) ≫ (compRight βW βT).app K := by
    have hD := right_square_normalization V U T W (comapLowerStarIso a f) K
    change (compRight βW βT).app K ≫
      (derivedComapLowerStarIso a f).hom.app (DerivedCategory.Qh.obj K) =
        DerivedCategory.Qh.map (d.inv.app K) ≫ (compRight βU βV).app K at hD
    exact inverse_square ((compRight βU βV).app K)
      ((compRight βW βT).app K)
      ((derivedComapLowerStarIso a f).symm.app (DerivedCategory.Qh.obj K))
      (DerivedCategory.Qh.mapIso (d.app K)) hD
  have hz := localized_conjugate DerivedCategory.Qh DerivedCategory.Qh
    (HomotopyCategory.quasiIso _ (.up ℤ))
    ((ar.mapHomotopyCategory (.up ℤ)).comp (ax.mapHomotopyCategory (.up ℤ)))
    ((ay.mapHomotopyCategory (.up ℤ)).comp (as'.mapHomotopyCategory (.up ℤ)))
    (dr.comp dx) (dy.comp ds) (compLeft αF αE) (compLeft αG αH)
    (compRight βU βV) (compRight βW βT)
    (comp_normalization (ar.mapHomotopyCategory (.up ℤ)) (ax.mapHomotopyCategory (.up ℤ))
      dr dx αF αE βU βV hF hE)
    (comp_normalization (ay.mapHomotopyCategory (.up ℤ)) (as'.mapHomotopyCategory (.up ℤ))
      dy ds αG αH βW βT hG hH)
    e d he (coefficientScalarPathIso a f) (derivedComapLowerStarIso a f).symm hα hβ
  apply Iso.ext
  rw [derivedPullIso]
  exact hz

end AlgebraicGeometry.ProEtale.CondensedRing
