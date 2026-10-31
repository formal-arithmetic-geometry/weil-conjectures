/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.EtaleCoefficientTransportInterfaces
import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleTransportAssociator
import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleInverseTransportComposition

/-! # Composition of normalized compact-support coefficient projections

Source: Zheng, Construction 5.15 and Proposition 2.29(2).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Functor SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
section
variable {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]
  {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
  {G G' : C ⥤ E} {H H' : D ⥤ F}

private theorem mate_natural
    (α : G ⋙ L₂ ⟶ L₁ ⋙ H) (α' : G' ⋙ L₂ ⟶ L₁ ⋙ H')
    (γ : G ⟶ G') (δ : H ⟶ H')
    (h : ∀ X, L₂.map (γ.app X) ≫ α'.app X = α.app X ≫ δ.app (L₁.obj X))
    (Y : D) :
    γ.app (R₁.obj Y) ≫ (mateEquiv adj₁ adj₂ α').app Y =
      (mateEquiv adj₁ adj₂ α).app Y ≫ R₂.map (δ.app Y) := by
  dsimp only [mateEquiv, Equiv.coe_fn_mk, NatTrans.comp_app, rightUnitor_inv_app,
    whiskerLeft_app, associator_hom_app, associator_inv_app, whiskerRight_app,
    Functor.comp_map, leftUnitor_hom_app, Functor.comp_obj, TwoSquare.natTrans]
  simp only [Functor.id_obj, Category.comp_id, Category.id_comp, Category.assoc]
  rw [← adj₂.unit_naturality_assoc]
  rw [← R₂.map_comp_assoc, h]
  rw [R₂.map_comp, Category.assoc, ← R₂.map_comp, ← δ.naturality]
  simp only [R₂.map_comp]

private theorem mate_natural_symm
    (β : R₁ ⋙ G ⟶ H ⋙ R₂) (β' : R₁ ⋙ G' ⟶ H' ⋙ R₂)
    (γ : G ⟶ G') (δ : H ⟶ H')
    (h : ∀ Y, γ.app (R₁.obj Y) ≫ β'.app Y = β.app Y ≫ R₂.map (δ.app Y))
    (X : C) :
    L₂.map (γ.app X) ≫ ((mateEquiv adj₁ adj₂).symm β').app X =
      ((mateEquiv adj₁ adj₂).symm β).app X ≫ δ.app (L₁.obj X) := by
  let α : G ⋙ L₂ ⟶ L₁ ⋙ H := ((mateEquiv adj₁ adj₂).symm β).natTrans
  let α' : G' ⋙ L₂ ⟶ L₁ ⋙ H' := ((mateEquiv adj₁ adj₂).symm β').natTrans
  change L₂.map (γ.app X) ≫ α'.app X = α.app X ≫ δ.app (L₁.obj X)
  have hα : adj₂.homEquiv _ _ (α.app X) =
      G.map (adj₁.unit.app X) ≫ β.app (L₁.obj X) :=
    (unit_mateEquiv_symm adj₁ adj₂ β X).symm
  have hα' : adj₂.homEquiv _ _ (α'.app X) =
      G'.map (adj₁.unit.app X) ≫ β'.app (L₁.obj X) :=
    (unit_mateEquiv_symm adj₁ adj₂ β' X).symm
  apply (adj₂.homEquiv _ _).injective
  rw [adj₂.homEquiv_naturality_left, adj₂.homEquiv_naturality_right, hα, hα']
  rw [← Category.assoc, ← γ.naturality]
  simp only [Functor.comp_obj, Category.assoc]
  rw [h]

end

section Three
variable {C₁ C₂ C₃ D₁ D₂ D₃ : Type u₁}
  [Category.{v₁} C₁] [Category.{v₁} C₂] [Category.{v₁} C₃]
  [Category.{v₁} D₁] [Category.{v₁} D₂] [Category.{v₁} D₃]
  {L₁ : C₁ ⥤ D₁} {R₁ : D₁ ⥤ C₁}
  {L₂ : C₂ ⥤ D₂} {R₂ : D₂ ⥤ C₂}
  {L₃ : C₃ ⥤ D₃} {R₃ : D₃ ⥤ C₃}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃)
  {G₁₂ : C₁ ⥤ C₂} {G₂₃ : C₂ ⥤ C₃} {G₁₃ : C₁ ⥤ C₃}
  {H₁₂ : D₁ ⥤ D₂} {H₂₃ : D₂ ⥤ D₃} {H₁₃ : D₁ ⥤ D₃}

private theorem left_mate_composition
    (α₁₂ : G₁₂ ⋙ L₂ ⟶ L₁ ⋙ H₁₂) (α₂₃ : G₂₃ ⋙ L₃ ⟶ L₂ ⋙ H₂₃)
    (α₁₃ : G₁₃ ⋙ L₃ ⟶ L₁ ⋙ H₁₃)
    (β₁₂ : R₁ ⋙ G₁₂ ⟶ H₁₂ ⋙ R₂) (β₂₃ : R₂ ⋙ G₂₃ ⟶ H₂₃ ⋙ R₃)
    (β₁₃ : R₁ ⋙ G₁₃ ⟶ H₁₃ ⋙ R₃)
    (h₁₂ : mateEquiv adj₁ adj₂ α₁₂ = β₁₂)
    (h₂₃ : mateEquiv adj₂ adj₃ α₂₃ = β₂₃)
    (h₁₃ : mateEquiv adj₁ adj₃ α₁₃ = β₁₃)
    (AG : G₁₂ ⋙ G₂₃ ⟶ G₁₃) (AH : H₁₂ ⋙ H₂₃ ⟶ H₁₃)
    (h : ∀ Y, AG.app (R₁.obj Y) ≫ β₁₃.app Y =
      G₂₃.map (β₁₂.app Y) ≫ β₂₃.app (H₁₂.obj Y) ≫ R₃.map (AH.app Y)) (X) :
    L₃.map (AG.app X) ≫ α₁₃.app X =
      α₂₃.app (G₁₂.obj X) ≫ H₂₃.map (α₁₂.app X) ≫ AH.app (L₁.obj X) := by
  let α := TwoSquare.hComp α₁₂ α₂₃
  have hm : mateEquiv adj₁ adj₃ α = TwoSquare.vComp β₁₂ β₂₃ := by
    rw [mateEquiv_vcomp adj₁ adj₂ adj₃, h₁₂, h₂₃]
  have hn := mate_natural_symm adj₁ adj₃ (mateEquiv adj₁ adj₃ α)
    (mateEquiv adj₁ adj₃ α₁₃) AG AH (by
      intro Y
      simpa only [hm, h₁₃, TwoSquare.vComp_app, TwoSquare.natTrans, Category.assoc]
        using h Y) X
  simpa only [Equiv.symm_apply_apply, α, TwoSquare.hComp_app,
    TwoSquare.natTrans, Category.assoc] using hn

private theorem right_mate_composition
    (α₁₂ : G₁₂ ⋙ L₂ ⟶ L₁ ⋙ H₁₂) (α₂₃ : G₂₃ ⋙ L₃ ⟶ L₂ ⋙ H₂₃)
    (α₁₃ : G₁₃ ⋙ L₃ ⟶ L₁ ⋙ H₁₃)
    (β₁₂ : R₁ ⋙ G₁₂ ⟶ H₁₂ ⋙ R₂) (β₂₃ : R₂ ⋙ G₂₃ ⟶ H₂₃ ⋙ R₃)
    (β₁₃ : R₁ ⋙ G₁₃ ⟶ H₁₃ ⋙ R₃)
    (h₁₂ : mateEquiv adj₁ adj₂ α₁₂ = β₁₂)
    (h₂₃ : mateEquiv adj₂ adj₃ α₂₃ = β₂₃)
    (h₁₃ : mateEquiv adj₁ adj₃ α₁₃ = β₁₃)
    (AG : G₁₂ ⋙ G₂₃ ⟶ G₁₃) (AH : H₁₂ ⋙ H₂₃ ⟶ H₁₃)
    (h : ∀ X, L₃.map (AG.app X) ≫ α₁₃.app X =
      α₂₃.app (G₁₂.obj X) ≫ H₂₃.map (α₁₂.app X) ≫ AH.app (L₁.obj X)) (Y) :
    AG.app (R₁.obj Y) ≫ β₁₃.app Y =
      G₂₃.map (β₁₂.app Y) ≫ β₂₃.app (H₁₂.obj Y) ≫ R₃.map (AH.app Y) := by
  let α := TwoSquare.hComp α₁₂ α₂₃
  have hm : mateEquiv adj₁ adj₃ α = TwoSquare.vComp β₁₂ β₂₃ := by
    rw [mateEquiv_vcomp adj₁ adj₂ adj₃, h₁₂, h₂₃]
  have hn := mate_natural adj₁ adj₃ α α₁₃ AG AH (by
    intro X
    simpa only [α, TwoSquare.hComp_app, TwoSquare.natTrans, Category.assoc] using h X) Y
  simpa only [hm, h₁₃, TwoSquare.vComp_app, TwoSquare.natTrans, Category.assoc] using hn

private theorem inverse_cocycle
    (U₁₂ : G₁₂ ⋙ L₂ ≅ L₁ ⋙ H₁₂) (U₂₃ : G₂₃ ⋙ L₃ ≅ L₂ ⋙ H₂₃)
    (U₁₃ : G₁₃ ⋙ L₃ ≅ L₁ ⋙ H₁₃)
    (AG : G₁₂ ⋙ G₂₃ ⟶ G₁₃) (AH : H₁₂ ⋙ H₂₃ ⟶ H₁₃)
    (h : ∀ X, L₃.map (AG.app X) ≫ U₁₃.hom.app X =
      U₂₃.hom.app (G₁₂.obj X) ≫ H₂₃.map (U₁₂.hom.app X) ≫ AH.app (L₁.obj X))
    (X) :
    AH.app (L₁.obj X) ≫ U₁₃.inv.app X =
      H₂₃.map (U₁₂.inv.app X) ≫ U₂₃.inv.app (G₁₂.obj X) ≫ L₃.map (AG.app X) := by
  apply (cancel_mono (U₁₃.hom.app X)).1
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [h]
  simp only [Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc,
    Iso.inv_hom_id_app]
  change AH.app (L₁.obj X) ≫ 𝟙 _ = H₂₃.map (𝟙 _) ≫ AH.app (L₁.obj X)
  rw [H₂₃.map_id, Category.comp_id, Category.id_comp]

private theorem right_inverse_cocycle
    (U₁₂ : R₁ ⋙ G₁₂ ≅ H₁₂ ⋙ R₂) (U₂₃ : R₂ ⋙ G₂₃ ≅ H₂₃ ⋙ R₃)
    (U₁₃ : R₁ ⋙ G₁₃ ≅ H₁₃ ⋙ R₃)
    (AG : G₁₂ ⋙ G₂₃ ⟶ G₁₃) (AH : H₁₂ ⋙ H₂₃ ⟶ H₁₃)
    (h : ∀ Y, AG.app (R₁.obj Y) ≫ U₁₃.hom.app Y =
      G₂₃.map (U₁₂.hom.app Y) ≫ U₂₃.hom.app (H₁₂.obj Y) ≫ R₃.map (AH.app Y))
    (Y) :
    R₃.map (AH.app Y) ≫ U₁₃.inv.app Y =
      U₂₃.inv.app (H₁₂.obj Y) ≫ G₂₃.map (U₁₂.inv.app Y) ≫ AG.app (R₁.obj Y) := by
  apply (cancel_epi (U₂₃.hom.app (H₁₂.obj Y))).1
  apply (cancel_epi (G₂₃.map (U₁₂.hom.app Y))).1
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc]
  simpa only [Category.assoc, Iso.hom_inv_id_app, Functor.comp_obj,
    G₂₃.map_id, Category.comp_id, Category.id_comp] using
    congrArg (fun t ↦ t ≫ U₁₃.inv.app Y) (h Y).symm

end Three

section Pasting
variable {C₁ C₂ C₃ D₁ D₂ D₃ E₁ E₂ E₃ : Type u₁}
  [Category.{v₁} C₁] [Category.{v₁} C₂] [Category.{v₁} C₃]
  [Category.{v₁} D₁] [Category.{v₁} D₂] [Category.{v₁} D₃]
  [Category.{v₁} E₁] [Category.{v₁} E₂] [Category.{v₁} E₃]
  {F₁ : C₁ ⥤ D₁} {F₂ : C₂ ⥤ D₂} {F₃ : C₃ ⥤ D₃}
  {R₁ : D₁ ⥤ E₁} {R₂ : D₂ ⥤ E₂} {R₃ : D₃ ⥤ E₃}
  {X₁₂ : C₁ ⥤ C₂} {X₂₃ : C₂ ⥤ C₃} {X₁₃ : C₁ ⥤ C₃}
  {Z₁₂ : D₁ ⥤ D₂} {Z₂₃ : D₂ ⥤ D₃} {Z₁₃ : D₁ ⥤ D₃}
  {Y₁₂ : E₁ ⥤ E₂} {Y₂₃ : E₂ ⥤ E₃} {Y₁₃ : E₁ ⥤ E₃}

private def projectionIso
    (A : X₁₂ ⋙ F₂ ≅ F₁ ⋙ Z₁₂) (B : R₁ ⋙ Y₁₂ ≅ Z₁₂ ⋙ R₂) :
    (F₁ ⋙ R₁) ⋙ Y₁₂ ≅ X₁₂ ⋙ (F₂ ⋙ R₂) :=
  Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ B ≪≫
    (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight A.symm _ ≪≫
      Functor.associator _ _ _

private theorem projection_composition
    (A₁₂ : X₁₂ ⋙ F₂ ≅ F₁ ⋙ Z₁₂) (A₂₃ : X₂₃ ⋙ F₃ ≅ F₂ ⋙ Z₂₃)
    (A₁₃ : X₁₃ ⋙ F₃ ≅ F₁ ⋙ Z₁₃)
    (B₁₂ : R₁ ⋙ Y₁₂ ≅ Z₁₂ ⋙ R₂) (B₂₃ : R₂ ⋙ Y₂₃ ≅ Z₂₃ ⋙ R₃)
    (B₁₃ : R₁ ⋙ Y₁₃ ≅ Z₁₃ ⋙ R₃)
    (AX : X₁₂ ⋙ X₂₃ ⟶ X₁₃) (AY : Y₁₂ ⋙ Y₂₃ ⟶ Y₁₃)
    (AZ : Z₁₂ ⋙ Z₂₃ ⟶ Z₁₃)
    (hopen : ∀ K, F₃.map (AX.app K) ≫ A₁₃.hom.app K =
      A₂₃.hom.app (X₁₂.obj K) ≫ Z₂₃.map (A₁₂.hom.app K) ≫ AZ.app (F₁.obj K))
    (hproper : ∀ K, R₃.map (AZ.app K) ≫ B₁₃.inv.app K =
      B₂₃.inv.app (Z₁₂.obj K) ≫ Y₂₃.map (B₁₂.inv.app K) ≫ AY.app (R₁.obj K))
    (K) :
    (F₃ ⋙ R₃).map (AX.app K) ≫ (projectionIso A₁₃ B₁₃).inv.app K =
      (projectionIso A₂₃ B₂₃).inv.app (X₁₂.obj K) ≫
        Y₂₃.map ((projectionIso A₁₂ B₁₂).inv.app K) ≫ AY.app ((F₁ ⋙ R₁).obj K) := by
  simp only [projectionIso, Iso.trans_inv, NatTrans.comp_app, associator_inv_app,
    associator_hom_app, isoWhiskerRight_inv, isoWhiskerLeft_inv, Iso.symm_inv,
    whiskerRight_app, whiskerLeft_app, Functor.comp_obj, Functor.comp_map,
    Category.comp_id, Category.id_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, hopen]
  simp only [Functor.map_comp, Category.assoc]
  rw [hproper]
  have hn : R₃.map (Z₂₃.map (A₁₂.hom.app K)) ≫
      B₂₃.inv.app (Z₁₂.obj (F₁.obj K)) =
      B₂₃.inv.app (F₂.obj (X₁₂.obj K)) ≫ Y₂₃.map (R₂.map (A₁₂.hom.app K)) :=
    B₂₃.inv.naturality (A₁₂.hom.app K)
  rw [← Category.assoc (R₃.map (Z₂₃.map (A₁₂.hom.app K))), hn]
  simp only [Category.assoc]

end Pasting

private theorem strictEtaleTransportAssociator_exists
    {O₁ O₂ O₃ : Type (u + 1)} [CommRing O₁] [CommRing O₂] [CommRing O₃]
    {ell₁ : O₁} {ell₂ : O₂} {ell₃ : O₃} {phi₁₂ : O₁ →+* O₂} {phi₂₃ : O₂ →+* O₃}
    {r₁₂ r₂₃ : ℕ →o ℕ}
    {a : StrictEtaleCoefficientChange O₁ O₂ ell₁ ell₂ phi₁₂ r₁₂}
    {b : StrictEtaleCoefficientChange O₂ O₃ ell₂ ell₃ phi₂₃ r₂₃}
    {T : Scheme.{u}}
    {P₁ : StrictEtaleEvaluation T O₁ ell₁}
    {P₂ : StrictEtaleEvaluation T O₂ ell₂}
    {P₃ : StrictEtaleEvaluation T O₃ ell₃}
    (U₁₂ : StrictEtaleCoefficientTransport a T P₁ P₂)
    (U₂₃ : StrictEtaleCoefficientTransport b T P₂ P₃)
    (U₁₃ : StrictEtaleCoefficientTransport (a.comp b) T P₁ P₃) :
    Nonempty (StrictEtaleTransportComposition U₁₂ U₂₃ U₁₃) := by
  obtain ⟨e, he⟩ := strictEtaleOrdinaryTransportAssociator_exists U₁₂ U₂₃ U₁₃
  let W := HomologicalComplex.quasiIso (strictEtaleCoefficientSystem T O₁ ell₁) (.up ℤ)
  let F₁₂ := U₁₂.ordinary.mapHomologicalComplex (.up ℤ)
  let F₂₃ := U₂₃.ordinary.mapHomologicalComplex (.up ℤ)
  let F₁₃ := U₁₃.ordinary.mapHomologicalComplex (.up ℤ)
  let factors : DerivedCategory.Q ⋙ (U₁₂.derived ⋙ U₂₃.derived) ≅
      (F₁₂ ⋙ F₂₃) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight U₁₂.factors U₂₃.derived ≪≫ Functor.associator _ _ _ ≪≫
        isoWhiskerLeft F₁₂ U₂₃.factors ≪≫ (Functor.associator _ _ _).symm
  let : Localization.Lifting DerivedCategory.Q W
      ((F₁₂ ⋙ F₂₃) ⋙ DerivedCategory.Q) (U₁₂.derived ⋙ U₂₃.derived) := ⟨factors⟩
  let : Localization.Lifting DerivedCategory.Q W
      (F₁₃ ⋙ DerivedCategory.Q) U₁₃.derived := ⟨U₁₃.factors⟩
  let ec : (F₁₂ ⋙ F₂₃) ⋙ DerivedCategory.Q ≅ F₁₃ ⋙ DerivedCategory.Q :=
    isoWhiskerRight (Functor.mapHomologicalComplexCompIso e (.up ℤ)) DerivedCategory.Q
  let d : U₁₂.derived ⋙ U₂₃.derived ≅ U₁₃.derived :=
    Localization.liftNatIso DerivedCategory.Q W _ _ _ _ ec
  refine ⟨⟨(e, d), he, ?_⟩⟩
  intro K
  have hd : d.hom.app (DerivedCategory.Q.obj K) =
      factors.hom.app K ≫ ec.hom.app K ≫ U₁₃.factors.inv.app K :=
    Localization.liftNatTrans_app DerivedCategory.Q W _ _ _ _ ec.hom K
  rw [hd]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  dsimp only [factors, ec, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    associator_inv_app, associator_hom_app, isoWhiskerRight_hom, isoWhiskerLeft_hom,
    whiskerRight_app, whiskerLeft_app, Category.id_comp, Category.comp_id,
    Functor.mapHomologicalComplexCompIso, Functor.comp_obj, Functor.id_obj, F₁₂, F₂₃, F₁₃]
  simp only [Category.comp_id, Category.id_comp, Category.assoc]

/-- The tensor associators intertwine the inverse compact-support projection squares.
Source: Zheng, Construction 5.15 and Proposition 2.29(2)
(blueprint: lem-pur-strict-etale-compact-support-composition).

Proof: at each coefficient level the two successive extension functors and the single
extension along the composite map are left adjoint to the same restriction functor.
The identity on underlying sections identifies the restrictions, so uniqueness of left
adjoints gives a tensor associator. Its composite with the two tensor units is the
single tensor unit. Apply this formula to successor transitions: the quotient ring
maps commute with both coefficient maps by their generator equations. The tensor
adjunction then gives compatibility with transitions. The resulting level maps form
an isomorphism of ordinary strict systems, natural in their componentwise morphisms.
Exact localization on complexes gives AX, AY and AZ with the displayed representative
normalizations. For each geometric inverse-image square, paste the two normalized
squares. Its action after the composite tensor unit equals that of the single square:
both are the pullback of the same unit on underlying set sheaves. Uniqueness in the
tensor adjunction and faithful forgetting give equality of the ordinary squares.
Their representative equations descend this equality through localization; equality
is checked after Q, not after derived evaluation. Pasting adjunction mates transfers
it to the open-extension and proper-direct-image squares. Substitute these two
identities in the definition of projection, use naturality of the associators, and
cancel the adjacent inverse isomorphisms. The remaining equation is exactly the
inverse projection cocycle below. No exceptional adjoint or quotient flatness is used.
-/
theorem strictEtaleCompactSupportTransport_composition
    {O₁ O₂ O₃ : Type (u + 1)} [CommRing O₁] [CommRing O₂] [CommRing O₃]
    {ell₁ : O₁} {ell₂ : O₂} {ell₃ : O₃} {phi₁₂ : O₁ →+* O₂} {phi₂₃ : O₂ →+* O₃}
    {r₁₂ r₂₃ : ℕ →o ℕ}
    {a : StrictEtaleCoefficientChange O₁ O₂ ell₁ ell₂ phi₁₂ r₁₂}
    {b : StrictEtaleCoefficientChange O₂ O₃ ell₂ ell₃ phi₂₃ r₂₃}
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    {S₁ : StrictEtaleCompactSupport O₁ ell₁ c}
    {S₂ : StrictEtaleCompactSupport O₂ ell₂ c}
    {S₃ : StrictEtaleCompactSupport O₃ ell₃ c}
    {X₁₂ : StrictEtaleCoefficientTransport a X S₁.PX S₂.PX}
    {Y₁₂ : StrictEtaleCoefficientTransport a Y S₁.PY S₂.PY}
    {Z₁₂ : StrictEtaleCoefficientTransport a c.Z S₁.PZ S₂.PZ}
    {X₂₃ : StrictEtaleCoefficientTransport b X S₂.PX S₃.PX}
    {Y₂₃ : StrictEtaleCoefficientTransport b Y S₂.PY S₃.PY}
    {Z₂₃ : StrictEtaleCoefficientTransport b c.Z S₂.PZ S₃.PZ}
    {X₁₃ : StrictEtaleCoefficientTransport (a.comp b) X S₁.PX S₃.PX}
    {Y₁₃ : StrictEtaleCoefficientTransport (a.comp b) Y S₁.PY S₃.PY}
    {Z₁₃ : StrictEtaleCoefficientTransport (a.comp b) c.Z S₁.PZ S₃.PZ}
    (P₁₂ : StrictEtaleCompactSupportTransport a c S₁ S₂ X₁₂ Y₁₂ Z₁₂)
    (P₂₃ : StrictEtaleCompactSupportTransport b c S₂ S₃ X₂₃ Y₂₃ Z₂₃)
    (P₁₃ : StrictEtaleCompactSupportTransport (a.comp b) c S₁ S₃ X₁₃ Y₁₃ Z₁₃) :
    ∃ (AX : StrictEtaleTransportComposition X₁₂ X₂₃ X₁₃)
      (AY : StrictEtaleTransportComposition Y₁₂ Y₂₃ Y₁₃)
      (_AZ : StrictEtaleTransportComposition Z₁₂ Z₂₃ Z₁₃),
      ∀ K, S₃.functor.map (AX.derived.hom.app K) ≫ P₁₃.projection.inv.app K =
        P₂₃.projection.inv.app (X₁₂.derived.obj K) ≫
          Y₂₃.derived.map (P₁₂.projection.inv.app K) ≫
            AY.derived.hom.app (S₁.functor.obj K) := by
  obtain ⟨AX⟩ := strictEtaleTransportAssociator_exists X₁₂ X₂₃ X₁₃
  obtain ⟨AY⟩ := strictEtaleTransportAssociator_exists Y₁₂ Y₂₃ Y₁₃
  obtain ⟨AZ⟩ := strictEtaleTransportAssociator_exists Z₁₂ Z₂₃ Z₁₃
  have hopen (K) : S₃.derivedOpen.map (AX.derived.hom.app K) ≫
      P₁₃.openComparison.hom.app K =
      P₂₃.openComparison.hom.app (X₁₂.derived.obj K) ≫
        Z₂₃.derived.map (P₁₂.openComparison.hom.app K) ≫
          AZ.derived.hom.app (S₁.derivedOpen.obj K) := by
    apply left_mate_composition S₁.derivedOpenAdjunction S₂.derivedOpenAdjunction
      S₃.derivedOpenAdjunction P₁₂.openComparison.hom P₂₃.openComparison.hom
      P₁₃.openComparison.hom P₁₂.val.openSquare.derived.inv P₂₃.val.openSquare.derived.inv
      P₁₃.val.openSquare.derived.inv P₁₂.property.1 P₂₃.property.1 P₁₃.property.1
      AX.derived.hom AZ.derived.hom
    exact inverse_cocycle P₁₂.val.openSquare.derived P₂₃.val.openSquare.derived
      P₁₃.val.openSquare.derived AZ.derived.hom AX.derived.hom
      (strictEtaleInverseTransport_composition P₁₂.val.openSquare
        P₂₃.val.openSquare P₁₃.val.openSquare AX AZ)
  have hproper (K) :
      S₃.properDerived.system.direct.map (AZ.derived.hom.app K) ≫
        P₁₃.properComparison.inv.app K =
      P₂₃.properComparison.inv.app (Z₁₂.derived.obj K) ≫
        Y₂₃.derived.map (P₁₂.properComparison.inv.app K) ≫
          AY.derived.hom.app (S₁.properDerived.system.direct.obj K) := by
    apply right_inverse_cocycle P₁₂.properComparison P₂₃.properComparison
      P₁₃.properComparison AY.derived.hom AZ.derived.hom
    intro L
    exact right_mate_composition S₁.properDerived.system.adjunction
      S₂.properDerived.system.adjunction S₃.properDerived.system.adjunction
      P₁₂.val.properSquare.derived.hom P₂₃.val.properSquare.derived.hom
      P₁₃.val.properSquare.derived.hom P₁₂.properComparison.hom P₂₃.properComparison.hom
      P₁₃.properComparison.hom P₁₂.property.2.symm P₂₃.property.2.symm P₁₃.property.2.symm
      AY.derived.hom AZ.derived.hom
      (strictEtaleInverseTransport_composition P₁₂.val.properSquare
        P₂₃.val.properSquare P₁₃.val.properSquare AZ AY) L
  refine ⟨AX, AY, AZ, ?_⟩
  exact projection_composition P₁₂.openComparison P₂₃.openComparison P₁₃.openComparison
    P₁₂.properComparison P₂₃.properComparison P₁₃.properComparison
    AX.derived.hom AY.derived.hom AZ.derived.hom hopen hproper


end AlgebraicGeometry
