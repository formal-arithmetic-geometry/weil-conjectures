/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.FiniteTensorSignedReduction
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.CategoryTheory.DerivedCategory.SixFunctors.NativeDerivedClosedTensorShifts
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Scalar.FiniteScalarTensorSource

/-! # One-variable shift compatibility of the normalized finite tensor comparison

Source: Stacks 07A4 and 0FNH, parent proof Step 6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace WeilConjectures.PurityFiniteSetting

private def transposeComparison
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    {E : A ⥤ B} {U : B ⥤ A} (a : E ⊣ U)
    (QA : A ⥤ C) (QB : B ⥤ D) {L : C ⥤ D} {R : D ⥤ C}
    (b : L ⊣ R) (e : QB ⋙ R ≅ U ⋙ QA) : QA ⋙ L ⟶ E ⋙ QB :=
  whiskerRight ((leftUnitor QA).inv ≫ whiskerRight a.unit QA ≫
    (Functor.associator _ _ _).hom ≫ whiskerLeft E e.inv ≫
    (Functor.associator _ _ _).inv) L ≫
      (Functor.associator _ _ _).hom ≫ whiskerLeft (E ⋙ QB) b.counit ≫
      (rightUnitor (E ⋙ QB)).hom

private theorem transposeComparison_app
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    {E : A ⥤ B} {U : B ⥤ A} (a : E ⊣ U)
    (QA : A ⥤ C) (QB : B ⥤ D) {L : C ⥤ D} {R : D ⥤ C}
    (b : L ⊣ R) (e : QB ⋙ R ≅ U ⋙ QA) (X : A) :
    (transposeComparison a QA QB b e).app X =
      (b.homEquiv _ _).symm (QA.map (a.unit.app X) ≫ e.inv.app (E.obj X)) := by
  simp [transposeComparison, Adjunction.homEquiv_counit]

private theorem transposeComparison_shift
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ] [HasShift D ℤ]
    {E : A ⥤ B} {U : B ⥤ A} (a : E ⊣ U)
    (QA : A ⥤ C) (QB : B ⥤ D) {L : C ⥤ D} {R : D ⥤ C}
    [E.CommShift ℤ] [U.CommShift ℤ] [QA.CommShift ℤ] [QB.CommShift ℤ]
    [L.CommShift ℤ] [R.CommShift ℤ] [NatTrans.CommShift a.unit ℤ]
    (b : L ⊣ R) [b.CommShift ℤ] (e : QB ⋙ R ≅ U ⋙ QA)
    [NatTrans.CommShift e.hom ℤ] :
    NatTrans.CommShift (transposeComparison a QA QB b e) ℤ := by
  unfold transposeComparison
  infer_instance

private theorem cochainAdjunction_unit
    {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
    {E : A ⥤ B} {U : B ⥤ A} [E.Additive] [U.Additive] (adj : E ⊣ U)
    (X : CochainComplex A ℤ) :
    (adj.mapHomologicalComplex (.up ℤ)).unit.app X =
      (mapHomologicalComplexIdIso _ (.up ℤ)).inv.app X ≫
        (NatTrans.mapHomologicalComplex adj.unit (.up ℤ)).app X ≫
        (mapHomologicalComplexCompIso (Iso.refl (E ⋙ U)) (.up ℤ)).inv.app X := by
  ext i : 1
  simp only [Functor.id_obj, Functor.comp_obj, Adjunction.mapHomologicalComplex_unit_app_f,
    HomologicalComplex.comp_f, mapHomologicalComplexIdIso_inv_app_f,
    NatTrans.mapHomologicalComplex_app_f, mapHomologicalComplexCompIso_inv_app_f,
    Iso.refl_inv, NatTrans.id_app]
  exact ((Category.id_comp (adj.unit.app (X.X i) ≫ 𝟙 ((E ⋙ U).obj (X.X i)))).trans
    (Category.comp_id (adj.unit.app (X.X i)))).symm

-- Shift compatibility is detected after restriction to an essentially surjective
-- family of resolving representatives; no exactness of scalar extension is used.

private theorem normalized_core_shift_second
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    [MonoidalCategory A] [MonoidalCategory B] [MonoidalCategory C] [MonoidalCategory D]
    [Preadditive A] [Preadditive B] [Preadditive C] [Preadditive D]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor A n).Additive] [∀ n : ℤ, (shiftFunctor B n).Additive]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [(curriedTensor A).CommShift₂Int] [(curriedTensor B).CommShift₂Int]
    [(curriedTensor C).CommShift₂Int] [(curriedTensor D).CommShift₂Int]
    (QA : A ⥤ C) (QB : B ⥤ D) (E : A ⥤ B) (L : C ⥤ D)
    [QA.CommShift ℤ] [QB.CommShift ℤ] [E.CommShift ℤ] [L.CommShift ℤ]
    [QA.LaxMonoidal] [QB.LaxMonoidal]
    (h : L.CoreMonoidal) (S : ObjectProperty A) [S.IsStableUnderShift ℤ]
    (c : QA ⋙ L ⟶ E ⋙ QB) [NatTrans.CommShift c ℤ]
    (d : (postcompose₂.obj E).obj (curriedTensor A) ⟶
      (((whiskeringLeft₂ _).obj E).obj E).obj (curriedTensor B))
    (hQA : ∀ X, NatTrans.CommShift
      (F₁ := QA ⋙ (curriedTensor C).obj (QA.obj X))
      (F₂ := (curriedTensor A).obj X ⋙ QA) ((LaxMonoidal.μNatTrans QA).app X) ℤ)
    (hQB : ∀ X, NatTrans.CommShift
      (F₁ := QB ⋙ (curriedTensor D).obj (QB.obj X))
      (F₂ := (curriedTensor B).obj X ⋙ QB) ((LaxMonoidal.μNatTrans QB).app X) ℤ)
    (hd : ∀ X, NatTrans.CommShift
      (F₁ := (curriedTensor A).obj X ⋙ E)
      (F₂ := E ⋙ (curriedTensor B).obj (E.obj X)) (d.app X) ℤ)
    (hn : ∀ X Y, S X → S Y →
      L.map (LaxMonoidal.μ QA X Y) ≫ c.app (X ⊗ Y) ≫ QB.map ((d.app X).app Y) =
        (h.μIso (QA.obj X) (QA.obj Y)).inv ≫ (c.app X ⊗ₘ c.app Y) ≫
          LaxMonoidal.μ QB (E.obj X) (E.obj Y))
    (hi : ∀ X Y, S X → S Y →
      IsIso (L.map (LaxMonoidal.μ QA X Y) ≫ c.app (X ⊗ Y) ≫
        QB.map ((d.app X).app Y)))
    (hr : ∀ U, ∃ X, S X ∧ Nonempty (QA.obj X ≅ U)) :
    ∀ (U V : C) (n : ℤ),
      L.map ((((curriedTensor C).obj U).commShiftIso n).hom.app V) ≫
          (L.commShiftIso n).hom.app (U ⊗ V) ≫ (h.μIso U V).inv⟦n⟧' =
        (h.μIso U (V⟦n⟧)).inv ≫ L.obj U ◁ (L.commShiftIso n).hom.app V ≫
          (((curriedTensor D).obj (L.obj U)).commShiftIso n).hom.app (L.obj V) := by
  let := h.toMonoidal
  have hδ (U V : C) : OplaxMonoidal.δ L U V = (h.μIso U V).inv := rfl
  have hon (X : A) (hX : S X) :
      NatTrans.CommShift
        (F₁ := (curriedTensor C).obj (QA.obj X) ⋙ L)
        (F₂ := L ⋙ (curriedTensor D).obj (L.obj (QA.obj X)))
        ((OplaxMonoidal.δNatTrans L).app (QA.obj X)) ℤ := by
    let μA : QA ⋙ (curriedTensor C).obj (QA.obj X) ⟶
        (curriedTensor A).obj X ⋙ QA := (LaxMonoidal.μNatTrans QA).app X
    let μB : QB ⋙ (curriedTensor D).obj (QB.obj (E.obj X)) ⟶
        (curriedTensor B).obj (E.obj X) ⋙ QB := (LaxMonoidal.μNatTrans QB).app (E.obj X)
    have : NatTrans.CommShift μA ℤ := hQA X
    have : NatTrans.CommShift μB ℤ := hQB (E.obj X)
    have := hd X
    have := Functor.CommShift₂.commShift_map
      (G := curriedTensor D) (h := .int) (c.app X)
    let τ : (curriedTensor C).obj (QA.obj X) ⋙ L ⟶
        L ⋙ (curriedTensor D).obj (L.obj (QA.obj X)) :=
      (OplaxMonoidal.δNatTrans L).app (QA.obj X)
    let c₂ : QA ⋙ ((curriedTensor C).obj (QA.obj X) ⋙ L) ⟶
        ((curriedTensor A).obj X ⋙ E) ⋙ QB :=
      (Functor.associator _ _ _).inv ≫ whiskerRight μA L ≫
        (Functor.associator _ _ _).hom ≫ whiskerLeft ((curriedTensor A).obj X) c ≫
        (Functor.associator _ _ _).inv
    let δ₀ : ((curriedTensor A).obj X ⋙ E) ⋙ QB ⟶
        (E ⋙ (curriedTensor B).obj (E.obj X)) ⋙ QB :=
      whiskerRight (d.app X) QB
    let c₁ : QA ⋙ (L ⋙ (curriedTensor D).obj (L.obj (QA.obj X))) ⟶
        (E ⋙ (curriedTensor B).obj (E.obj X)) ⋙ QB :=
      (Functor.associator _ _ _).inv ≫
        whiskerLeft (QA ⋙ L) ((curriedTensor D).map (c.app X)) ≫
        whiskerRight c ((curriedTensor D).obj (QB.obj (E.obj X))) ≫
        (Functor.associator _ _ _).hom ≫
        whiskerLeft E μB ≫
        (Functor.associator _ _ _).inv
    have : NatTrans.CommShift c₁ ℤ := by dsimp only [c₁]; infer_instance
    have : NatTrans.CommShift c₂ ℤ := by dsimp only [c₂]; infer_instance
    have : NatTrans.CommShift δ₀ ℤ := by dsimp only [δ₀]; infer_instance
    have ht (Y : A) (hY : S Y) : IsIso (c₁.app Y) := by
      have hs := hi X Y hX hY
      have he : c₁.app Y = (h.μIso (QA.obj X) (QA.obj Y)).hom ≫
          (L.map (LaxMonoidal.μ QA X Y) ≫ c.app (X ⊗ Y) ≫
            QB.map ((d.app X).app Y)) := by
        rw [hn X Y hX hY]
        simp only [Iso.hom_inv_id_assoc]
        simp [c₁, μB, MonoidalCategory.tensorHom_def]
      rw [he]
      infer_instance
    have : ∀ Y : S.FullSubcategory, IsIso ((whiskerLeft S.ι c₁).app Y) :=
      fun Y ↦ ht Y.obj Y.property
    have : IsIso (whiskerLeft S.ι c₁) := NatIso.isIso_of_isIso_app _
    have : NatTrans.CommShift (inv (whiskerLeft S.ι c₁)) ℤ :=
      NatTrans.CommShift.of_isIso _ ℤ
    have fac : whiskerLeft S.ι (whiskerLeft QA τ) ≫ whiskerLeft S.ι c₁ =
        whiskerLeft S.ι c₂ ≫ whiskerLeft S.ι δ₀ := by
      ext Y
      simpa [c₁, c₂, δ₀, τ, μA, μB, MonoidalCategory.tensorHom_def, Category.assoc,
        hδ] using
        (hn X Y.obj hX Y.property).symm
    have : NatTrans.CommShift (whiskerLeft S.ι (whiskerLeft QA τ)) ℤ := by
      rw [(IsIso.eq_comp_inv (whiskerLeft S.ι c₁)).2 fac]
      infer_instance
    have he : whiskerLeft (S.ι ⋙ QA) τ =
        (Functor.associator _ _ _).hom ≫ whiskerLeft S.ι (whiskerLeft QA τ) ≫
          (Functor.associator _ _ _).inv := by
      simp only [whiskerLeft_twice, Category.assoc, Iso.hom_inv_id_assoc,
        Iso.hom_inv_id, Category.comp_id]
    have : NatTrans.CommShift (whiskerLeft (S.ι ⋙ QA) τ) ℤ := by
      rw [he]
      infer_instance
    exact NatTrans.CommShift.of_whiskerLeft τ (S.ι ⋙ QA) (fun U ↦ by
      obtain ⟨Y, hY, ⟨e⟩⟩ := hr U
      exact ⟨⟨Y, hY⟩, e.inv, inferInstance⟩)
  have hall (U : C) : NatTrans.CommShift
      (F₁ := (curriedTensor C).obj U ⋙ L)
      (F₂ := L ⋙ (curriedTensor D).obj (L.obj U))
      ((OplaxMonoidal.δNatTrans L).app U) ℤ := by
    obtain ⟨X, hX, ⟨e⟩⟩ := hr U
    let τX : (curriedTensor C).obj (QA.obj X) ⋙ L ⟶
        L ⋙ (curriedTensor D).obj (L.obj (QA.obj X)) :=
      (OplaxMonoidal.δNatTrans L).app (QA.obj X)
    let τU : (curriedTensor C).obj U ⋙ L ⟶
        L ⋙ (curriedTensor D).obj (L.obj U) := (OplaxMonoidal.δNatTrans L).app U
    have : NatTrans.CommShift τX ℤ := hon X hX
    have := Functor.CommShift₂.commShift_map (G := curriedTensor C) (h := .int) e.inv
    have := Functor.CommShift₂.commShift_map
      (G := curriedTensor D) (h := .int) (L.map e.hom)
    change NatTrans.CommShift τU ℤ
    have he : τU =
        whiskerRight ((curriedTensor C).map e.inv) L ≫
          τX ≫ whiskerLeft L ((curriedTensor D).map (L.map e.hom)) := by
      ext V
      have hn := congr_app ((OplaxMonoidal.δNatTrans L).naturality e.inv) V
      dsimp [τU, τX] at hn ⊢
      rw [reassoc_of% hn, ← comp_whiskerRight, ← L.map_comp, e.inv_hom_id,
        L.map_id, id_whiskerRight, Category.comp_id]
    rw [he]
    infer_instance
  intro U V n
  have := hall U
  simpa only [Functor.commShiftIso_comp_hom_app, NatTrans.comp_app,
    whiskerLeft_app, whiskerRight_app, Category.assoc, OplaxMonoidal.δNatTrans_app_app,
    hδ, curriedTensor_obj_map, curriedTensor_obj_obj, Functor.comp_obj] using
    NatTrans.shift_app_comm
      (F₁ := (curriedTensor C).obj U ⋙ L)
      (F₂ := L ⋙ (curriedTensor D).obj (L.obj U))
      ((OplaxMonoidal.δNatTrans L).app U) n V

-- The tensorator of Q is compatible with the native derived tensor shift.

private theorem localization_tensor_shift
    {C : Type*} [Category.{v} C] [Abelian C]
    [IsGrothendieckAbelian.{v} C] [HasDerivedCategory.{w} C]
    [MonoidalCategory C] [MonoidalClosed C]
    [MonoidalPreadditive C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    (X : CochainComplex C ℤ) :
    NatTrans.CommShift
      (F₁ := _root_.DerivedCategory.Q ⋙
        (curriedTensor (_root_.DerivedCategory C)).obj (_root_.DerivedCategory.Q.obj X))
      (F₂ := (curriedTensor (CochainComplex C ℤ)).obj X ⋙ _root_.DerivedCategory.Q)
      ((LaxMonoidal.μNatTrans (_root_.DerivedCategory.Q (C := C))).app X) ℤ := by
  constructor
  intro n
  ext Y
  have he := (_root_.DerivedCategory.nativeDerivedClosedTensorShifts C).2.2.1 X Y n
  have ht : (((curriedTensor (CochainComplex C ℤ)).obj X).commShiftIso n).hom.app Y =
      (CochainComplex.mapBifunctorShift₂Iso X Y (curriedTensor C) n).hom := by
    exact Functor.commShiftIso_map₂CochainComplex_hom_app (curriedTensor C) X Y n
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    Functor.commShiftIso_comp_hom_app, Category.assoc,
    LaxMonoidal.μNatTrans_app_app] at ⊢
  rw [ht]
  simp only [Functor.uncurry_obj_map, Functor.comp_obj, curriedTensor_obj_map,
    curriedTensor_map_app, curriedTensor_obj_obj,
    MonoidalCategory.id_whiskerRight, Category.id_comp] at he
  convert he.symm using 1 <;> rfl

@[irreducible] private def scalarAdjunction
    {R₀ R₁ : Type (u + 1)} [CommRing R₀] [CommRing R₁]
    (φ : R₀ →+* R₁) (T : Scheme.{u}) :
    ProEtale.SupportedEtaleTensorOrigin.proFixedScalar φ T ⊣
      ProEtale.SupportedEtaleTensorOrigin.proFixedRestriction φ T :=
  Adjunction.ofIsRightAdjoint
    (ProEtale.SupportedEtaleTensorOrigin.proFixedRestriction φ T)

@[irreducible] private def scalarShiftData
    {R₀ R₁ : Type (u + 1)} [CommRing R₀] [CommRing R₁]
    (φ : R₀ →+* R₁) (T : Scheme.{u}) :
    { s : (ProEtale.SupportedEtaleTensorOrigin.proFixedScalar φ T).CommShift ℤ //
      letI := s
      (scalarAdjunction φ T).CommShift ℤ } :=
  ⟨(scalarAdjunction φ T).leftAdjointCommShift ℤ,
    (scalarAdjunction φ T).commShift_of_rightAdjoint ℤ⟩

@[instance_reducible] private def scalarShift
    {R₀ R₁ : Type (u + 1)} [CommRing R₀] [CommRing R₁]
    (φ : R₀ →+* R₁) (T : Scheme.{u}) :
    (ProEtale.SupportedEtaleTensorOrigin.proFixedScalar φ T).CommShift ℤ :=
  (scalarShiftData φ T).1

private theorem scalarShift_compatible
    {R₀ R₁ : Type (u + 1)} [CommRing R₀] [CommRing R₁]
    (φ : R₀ →+* R₁) (T : Scheme.{u}) :
    letI := scalarShift φ T
    (scalarAdjunction φ T).CommShift ℤ := by
  dsimp +instances only [scalarShift]
  exact (scalarShiftData φ T).2

@[irreducible] private def scalarComparison
    {R₀ R₁ : Type (u + 1)} [CommRing R₀] [CommRing R₁]
    (φ : R₀ →+* R₁) (T : Scheme.{u}) :
    letI := ProEtale.additive_sheafExtendScalars φ T
    _root_.DerivedCategory.Q ⋙
        ProEtale.SupportedEtaleTensorOrigin.proFixedScalar φ T ⟶
      (ProEtale.sheafExtendScalars φ T).mapHomologicalComplex (.up ℤ) ⋙
        _root_.DerivedCategory.Q := by
  letI := ProEtale.additive_sheafExtendScalars φ T
  letI : (Sheaf.restrictScalars (ProEt.topology T) φ).Additive :=
    ProEtale.additive_sheafComposeRestrictScalars φ T
  exact transposeComparison
    ((ProEtale.sheafExtendScalarsAdjunction φ T).mapHomologicalComplex (.up ℤ))
    _root_.DerivedCategory.Q _root_.DerivedCategory.Q (scalarAdjunction φ T)
    (Sheaf.restrictScalars (ProEt.topology T) φ).mapDerivedCategoryFactors

private theorem scalarComparison_app
    {R₀ R₁ : Type (u + 1)} [CommRing R₀] [CommRing R₁]
    (φ : R₀ →+* R₁) (T : Scheme.{u})
    (X : CochainComplex (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} R₀)) ℤ) :
    letI := ProEtale.additive_sheafExtendScalars φ T
    (scalarComparison φ T).app X =
      ProEtale.SupportedEtaleTensorOrigin.proScalarExtensionRepresentative φ T X := by
  delta scalarComparison
  rw [transposeComparison_app, cochainAdjunction_unit]
  delta scalarAdjunction
  rfl

private theorem scalarComparison_shift
    {R₀ R₁ : Type (u + 1)} [CommRing R₀] [CommRing R₁]
    (φ : R₀ →+* R₁) (T : Scheme.{u}) :
    letI := ProEtale.additive_sheafExtendScalars φ T
    letI := scalarShift φ T
    NatTrans.CommShift (scalarComparison φ T) ℤ := by
  let := ProEtale.additive_sheafExtendScalars φ T
  let : (Sheaf.restrictScalars (ProEt.topology T) φ).Additive :=
    ProEtale.additive_sheafComposeRestrictScalars φ T
  let := scalarShift φ T
  have : (scalarAdjunction φ T).CommShift ℤ := scalarShift_compatible φ T
  delta scalarComparison
  exact transposeComparison_shift _ _ _ _ _

private theorem abstract_cochain_tensor_shift
    {C D : Type*} [Category.{u} C] [Category.{v} D]
    [Abelian C] [Abelian D]
    [IsGrothendieckAbelian.{u} C] [IsGrothendieckAbelian.{v} D]
    [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalClosed C] [MonoidalClosed D]
    [MonoidalPreadditive C] [MonoidalPreadditive D]
    [BraidedCategory C] [BraidedCategory D]
    (G : C ⥤ D) [G.Additive] [G.OplaxMonoidal]
    [∀ j, PreservesColimitsOfShape
      (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) G]
    (X : CochainComplex C ℤ) :
    NatTrans.CommShift
      (F₁ := (curriedTensor (CochainComplex C ℤ)).obj X ⋙
        G.mapHomologicalComplex (.up ℤ))
      (F₂ := G.mapHomologicalComplex (.up ℤ) ⋙
        (curriedTensor (CochainComplex D ℤ)).obj
          ((G.mapHomologicalComplex (.up ℤ)).obj X))
      ((OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) G).app X) ℤ :=
  HomologicalComplex.commShift_mapBifunctorComparisonNatTrans_app
    (OplaxMonoidal.δNatTrans G) X

-- Keep the passage from cochains to derived categories abstract in the base categories.

private theorem normalized_derived_tensor_shift_second
    {A B : Type*} [Category.{v} A] [Category.{w} B]
    [Abelian A] [Abelian B]
    [IsGrothendieckAbelian.{v} A] [IsGrothendieckAbelian.{w} B]
    [HasDerivedCategory.{v} A] [HasDerivedCategory.{w} B]
    [MonoidalCategory A] [MonoidalCategory B]
    [MonoidalClosed A] [MonoidalClosed B]
    [MonoidalPreadditive A] [MonoidalPreadditive B]
    [BraidedCategory A] [BraidedCategory B]
    [Abelian.HasFunctorialFlatResolution A] [Abelian.HasFunctorialFlatResolution B]
    (G : A ⥤ B) [G.Additive] [G.OplaxMonoidal]
    [∀ j, PreservesColimitsOfShape
      (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) G]
    (L : _root_.DerivedCategory A ⥤ _root_.DerivedCategory B) [L.CommShift ℤ]
    (h : L.CoreMonoidal)
    (c : _root_.DerivedCategory.Q ⋙ L ⟶
      G.mapHomologicalComplex (.up ℤ) ⋙ _root_.DerivedCategory.Q)
    [NatTrans.CommShift c ℤ]
    (hn : ∀ (X Y : CochainComplex A ℤ),
      (HomologicalComplex.quasiIso A (.up ℤ)).kFlat X →
      (HomologicalComplex.quasiIso A (.up ℤ)).kFlat Y →
      L.map (LaxMonoidal.μ _root_.DerivedCategory.Q X Y) ≫ c.app (X ⊗ Y) ≫
        _root_.DerivedCategory.Q.map
          (((OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) G).app X).app Y) =
        (h.μIso (_root_.DerivedCategory.Q.obj X) (_root_.DerivedCategory.Q.obj Y)).inv ≫
          (c.app X ⊗ₘ c.app Y) ≫ LaxMonoidal.μ _root_.DerivedCategory.Q
            ((G.mapHomologicalComplex (.up ℤ)).obj X)
            ((G.mapHomologicalComplex (.up ℤ)).obj Y))
    (hi : ∀ (X Y : CochainComplex A ℤ),
      (HomologicalComplex.quasiIso A (.up ℤ)).kFlat X →
      (HomologicalComplex.quasiIso A (.up ℤ)).kFlat Y →
      IsIso (L.map (LaxMonoidal.μ _root_.DerivedCategory.Q X Y) ≫ c.app (X ⊗ Y) ≫
        _root_.DerivedCategory.Q.map
          (((OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) G).app X).app Y))) :
    ∀ (U V : _root_.DerivedCategory A) (n : ℤ),
      L.map ((((curriedTensor _).obj U).commShiftIso n).hom.app V) ≫
        (L.commShiftIso n).hom.app (U ⊗ V) ≫ (h.μIso U V).inv⟦n⟧' =
      (h.μIso U (V⟦n⟧)).inv ≫ L.obj U ◁ (L.commShiftIso n).hom.app V ≫
        ((((curriedTensor _).obj (L.obj U)).commShiftIso n).hom.app (L.obj V)) := by
  exact normalized_core_shift_second
    (_root_.DerivedCategory.Q (C := A)) (_root_.DerivedCategory.Q (C := B))
    (G.mapHomologicalComplex (.up ℤ)) L h
    (HomologicalComplex.quasiIso A (.up ℤ)).kFlat c
    (OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) G)
    (fun X ↦ localization_tensor_shift X) (fun X ↦ localization_tensor_shift X)
    (abstract_cochain_tensor_shift G) hn hi
    (_root_.DerivedCategory.nativeDerivedClosedTensorShifts A).2.2.2.2

private abbrev scalarCochainTensor
    {R₀ R₁ : Type (u + 1)} [CommRing R₀] [CommRing R₁]
    (φ : R₀ →+* R₁) (T : Scheme.{u}) :=
  OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ)
    (ProEtale.sheafExtendScalars φ T)

private theorem scalarCochainTensor_app
    {R₀ R₁ : Type (u + 1)} [CommRing R₀] [CommRing R₁]
    (φ : R₀ →+* R₁) (T : Scheme.{u})
    (X Y : CochainComplex (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} R₀)) ℤ) :
    ((scalarCochainTensor φ T).app X).app Y = finiteTensorCochainComparison φ T X Y := by
  delta finiteTensorCochainComparison
  rfl

private theorem scalarSource_normalized
    {R₀ R₁ : Type (u + 1)} [CommRing R₀] [CommRing R₁]
    (φ : R₀ →+* R₁) (T : Scheme.{u})
    (h : (ProEtale.SupportedEtaleTensorOrigin.proFixedScalar φ T).CoreMonoidal)
    (hn : (finiteScalarTensorData φ T).Normalized h)
    (X Y : CochainComplex (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} R₀)) ℤ)
    (hX : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat X)
    (hY : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Y) :
    (ProEtale.SupportedEtaleTensorOrigin.proFixedScalar φ T).map
        (LaxMonoidal.μ _root_.DerivedCategory.Q X Y) ≫
      (scalarComparison φ T).app (X ⊗ Y) ≫
        _root_.DerivedCategory.Q.map (((scalarCochainTensor φ T).app X).app Y) =
      (h.μIso (_root_.DerivedCategory.Q.obj X) (_root_.DerivedCategory.Q.obj Y)).inv ≫
        ((scalarComparison φ T).app X ⊗ₘ (scalarComparison φ T).app Y) ≫
          LaxMonoidal.μ _root_.DerivedCategory.Q
            (((ProEtale.sheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj X)
            (((ProEtale.sheafExtendScalars φ T).mapHomologicalComplex (.up ℤ)).obj Y) := by
  rw [scalarComparison_app φ T (X ⊗ Y), scalarComparison_app φ T X,
    scalarComparison_app φ T Y, scalarCochainTensor_app]
  have hn' := hn X Y hX hY
  unfold TensorRepresentativeData.source finiteScalarTensorData at hn'
  dsimp only [TensorRepresentativeData.obj] at hn'
  unfold cochainLocalizationTensor at hn'
  exact hn'

private theorem scalarSource_isIso
    {R₀ R₁ : Type (u + 1)} [CommRing R₀] [CommRing R₁]
    (φ : R₀ →+* R₁) (T : Scheme.{u})
    (X Y : CochainComplex (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} R₀)) ℤ)
    (hX : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat X)
    (hY : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Y) :
    IsIso ((ProEtale.SupportedEtaleTensorOrigin.proFixedScalar φ T).map
        (LaxMonoidal.μ _root_.DerivedCategory.Q X Y) ≫
      (scalarComparison φ T).app (X ⊗ Y) ≫
        _root_.DerivedCategory.Q.map (((scalarCochainTensor φ T).app X).app Y)) := by
  rw [scalarComparison_app φ T (X ⊗ Y), scalarCochainTensor_app]
  have hs := finiteScalarTensorData_source_isIso φ T X Y hX hY
  unfold TensorRepresentativeData.source finiteScalarTensorData at hs
  dsimp only [TensorRepresentativeData.obj] at hs
  unfold cochainLocalizationTensor at hs
  exact hs

private theorem fixedScalar_shift_second
    {R₀ R₁ : Type (u + 1)} [CommRing R₀] [CommRing R₁]
    (φ : R₀ →+* R₁) (T : Scheme.{u})
    (h : (ProEtale.SupportedEtaleTensorOrigin.proFixedScalar φ T).CoreMonoidal)
    (hn : (finiteScalarTensorData φ T).Normalized h)
    (U V : _root_.DerivedCategory
      (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} R₀))) (n : ℤ) :
    letI := scalarShift φ T
    (ProEtale.SupportedEtaleTensorOrigin.proFixedScalar φ T).map
        ((((curriedTensor _).obj U).commShiftIso n).hom.app V) ≫
      ((ProEtale.SupportedEtaleTensorOrigin.proFixedScalar φ T).commShiftIso n).hom.app
        (U ⊗ V) ≫ (h.μIso U V).inv⟦n⟧' =
    (h.μIso U (V⟦n⟧)).inv ≫
      (ProEtale.SupportedEtaleTensorOrigin.proFixedScalar φ T).obj U ◁
        ((ProEtale.SupportedEtaleTensorOrigin.proFixedScalar φ T).commShiftIso n).hom.app V ≫
      ((((curriedTensor _).obj
        ((ProEtale.SupportedEtaleTensorOrigin.proFixedScalar φ T).obj U)).commShiftIso n).hom.app
        ((ProEtale.SupportedEtaleTensorOrigin.proFixedScalar φ T).obj V)) := by
  let sL : (ProEtale.SupportedEtaleTensorOrigin.proFixedScalar φ T).CommShift ℤ :=
    scalarShift φ T
  have hc : NatTrans.CommShift (scalarComparison φ T) ℤ := scalarComparison_shift φ T
  have hshift := normalized_derived_tensor_shift_second
    (ProEtale.sheafExtendScalars φ T)
    (ProEtale.SupportedEtaleTensorOrigin.proFixedScalar φ T) h
    (scalarComparison φ T) (scalarSource_normalized φ T h hn) (scalarSource_isIso φ T)
  exact hshift U V n

/-- The normalized finite tensor comparison respects a shift in its second input.
Source: Stacks 07A4 and 0FNH, parent proof Step 6.
(blueprint: lem-pur-finite-tensor-shift-second).
Proof: Let E be ordinary scalar extension of cochain complexes and L the chosen
derived left adjoint of exact restriction. Transposing the cochain adjunction unit
through the exact restriction comparison gives c : Q ⋙ L ⟶ E ⋙ Q, whose components
are proScalarExtensionRepresentative and which commutes with every integer shift,
for the shift induced by the restriction adjunction. The tensorators of Q commute with
second-variable shifts by the native derived tensor normalization, and the cochain
scalar tensor comparison d commutes with them by the generic bifunctor-comparison shift
theorem (summand sign (-1)^(np), preserved by scalar extension). For a K-flat first
input X, normalization of finiteTensorCore expresses its inverse tensorator, restricted
to K-flat second inputs, as a composite of these shift-compatible maps followed by the
inverse of the tail, which is invertible on K-flat pairs since the recorded source is.
Every derived object is the localization of a K-flat complex, so shift compatibility
extends to all second inputs, and naturality of the tensorator along a representative
isomorphism extends it to all first inputs. The resulting commutation equation, with
the adjunction-induced finiteTensorScalarShift, is the displayed equality for every
integer n. -/
theorem finiteTensorShiftSecond (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m)
    (hmn : m ≤ P.level) (T : Scheme.{u})
    (U V : _root_.DerivedCategory
      (Sheaf (ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient))) (n : ℤ) :
    (P.finiteTensorReduction m hm hmn T).map
        ((((curriedTensor _).obj U).commShiftIso n).hom.app V) ≫
      (P.finiteTensorScalarShift m hm hmn T n).hom.app (U ⊗ V) ≫
      ((P.finiteTensorCore m hm hmn T).μIso U V).inv⟦n⟧' =
    ((P.finiteTensorCore m hm hmn T).μIso U (V⟦n⟧)).inv ≫
      (P.finiteTensorReduction m hm hmn T).obj U ◁
        ((P.finiteTensorScalarShift m hm hmn T n).hom.app V) ≫
      ((((curriedTensor _).obj ((P.finiteTensorReduction m hm hmn T).obj U)).commShiftIso n).hom.app
        ((P.finiteTensorReduction m hm hmn T).obj V)) := by
  have hn : (finiteScalarTensorData
      (P.finiteReductionRingHom m hm hmn).ulift.{u + 1, u + 1} T).Normalized
      (P.finiteTensorCore m hm hmn T) := by
    delta finiteTensorCore
    exact (P.existsUnique_finiteTensorCore m hm hmn T).choose_spec.1
  have hs := fixedScalar_shift_second (R₀ := P.Coefficient)
    (R₁ := (P.finiteReductionSetting m hm).Coefficient)
    (P.finiteReductionRingHom m hm hmn).ulift.{u + 1, u + 1}
    T (P.finiteTensorCore m hm hmn T) hn U V n
  have he : scalarShift (R₀ := P.Coefficient)
      (R₁ := (P.finiteReductionSetting m hm).Coefficient)
      (P.finiteReductionRingHom m hm hmn).ulift.{u + 1, u + 1} T =
        P.finiteTensorReductionCommShift m hm hmn T := by
    delta scalarShift scalarShiftData scalarAdjunction finiteTensorReductionCommShift
      finiteTensorAdjunction
    rfl
  rw [he] at hs
  dsimp +instances only [Coefficient, coefficientCommRing, finiteTensorReduction,
    finiteTensorScalarShift, ProEtale.SupportedEtaleTensorOrigin.proFixedScalar,
    ProEtale.SupportedEtaleTensorOrigin.fixedScalar] at hs ⊢
  exact hs

end WeilConjectures.PurityFiniteSetting
