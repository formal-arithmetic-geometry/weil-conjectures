/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedExceptionalReconstructionData
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsTriangleUnit

/-! # Realization properties for condensed exceptional reconstruction
Source: current blueprint sec-smooth-purity, reconstruction proof.
(blueprint: lem-pur-condensed-exceptional-realization-properties). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genCtorIdx false
attribute [local instance high] AlgebraicGeometry.strictEtaleLevelDerived
  AlgebraicGeometry.strictEtaleSystemDerived
  WeilConjectures.PurityFiniteSetting.clopenProEtaleSystemDerived
  WeilConjectures.PurityFiniteSetting.clopenProEtaleLevelDerived
attribute [local semireducible] AlgebraicGeometry.exceptionalProSystemDerived
  AlgebraicGeometry.exceptionalProLevelDerived
attribute [local irreducible] HasDerivedCategory.standard
attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory

namespace RegularRealizationProof
set_option backward.defeqAttrib.useBackward true
set_option Elab.async false
variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (F : C ⥤ D) (G : D ⥤ C) [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

private theorem factorh (P : CochainComplex C ℤ) :
    F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ _).obj P) =
      F.mapDerivedCategoryFactors.hom.app P := by
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  simp only [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso, Quotient.lift.isLift_hom,
    Quotient.lift.isLift_inv, Functor.mapHomotopyCategoryFactors]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.id_comp, Category.comp_id]

private theorem unit_cochain (adj : F ⊣ G)
    (ad : F.mapDerivedCategory ⊣ G.mapDerivedCategory)
    (h : ∀ K : HomotopyCategory C (.up ℤ),
      ad.unit.app (DerivedCategory.Qh.obj K) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app K) ≫
        G.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj K) =
          DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).unit.app K))
    (P : CochainComplex C ℤ) :
    ad.unit.app (DerivedCategory.Q.obj P) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
      G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) =
        DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app P) := by
  have hh := h ((HomotopyCategory.quotient _ _).obj P)
  rw [factorh] at hh
  change ad.unit.app (DerivedCategory.Q.obj P) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
      G.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ _).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj P)) = _ at hh
  rw [factorh] at hh
  rw [Adjunction.mapHomotopyCategory_unit_app_quotient] at hh
  exact hh

private theorem exact_single_unit (adj : F ⊣ G)
    (ad : F.mapDerivedCategory ⊣ G.mapDerivedCategory)
    (h : ∀ P : CochainComplex C ℤ,
      ad.unit.app (DerivedCategory.Q.obj P) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) =
          DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app P))
    (M : C) :
    ad.unit.app ((DerivedCategory.singleFunctor C 0).obj M) ≫
      G.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).hom.app M) ≫
      (G.mapDerivedCategorySingleFunctor 0).hom.app (F.obj M) =
        (DerivedCategory.singleFunctor C 0).map (adj.unit.app M) := by
  rw [F.mapDerivedCategorySingleFunctor_hom_app_eq,
    G.mapDerivedCategorySingleFunctor_hom_app_eq]
  simp only [Functor.map_comp, Category.assoc]
  erw [G.mapDerivedCategoryFactors_hom_naturality_assoc]
  have hh := congrArg (fun z ↦ z ≫ DerivedCategory.Q.map
    ((G.mapHomologicalComplex (.up ℤ)).map
      ((F.mapCochainComplexSingleFunctor 0).hom.app M)) ≫
        DerivedCategory.Q.map ((G.mapCochainComplexSingleFunctor 0).hom.app (F.obj M)))
      (h ((CochainComplex.singleFunctor _ 0).obj M))
  simp only [Category.assoc] at hh
  refine hh.trans ?_
  rw [← Functor.map_comp, ← Functor.map_comp]
  change DerivedCategory.Q.map _ = DerivedCategory.Q.map _
  congr 1
  apply HomologicalComplex.Hom.ext
  funext q
  by_cases hq : q = 0
  · subst q
    simp only [HomologicalComplex.comp_f, Adjunction.mapHomologicalComplex_unit_app_f,
      Functor.mapHomologicalComplex_map_f, Functor.mapCochainComplexSingleFunctor,
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
    dsimp only [CochainComplex.singleFunctor, CochainComplex.singleFunctors,
      Functor.comp_obj, Functor.id_obj]
    simp only [HomologicalComplex.single_map_f_self, Functor.map_comp, Category.assoc]
    rw [← G.map_comp_assoc
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (F.obj M)).inv
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (F.obj M)).hom,
      Iso.inv_hom_id, G.map_id, Category.id_comp]
    simpa only [Functor.id_map, Functor.comp_map, Category.assoc] using
      congrArg (fun f ↦ f ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (G.obj (F.obj M))).inv)
        (adj.unit.naturality (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).hom).symm
  · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M q hq).eq_of_src _ _

private theorem single_hom_of_unit (adj : F ⊣ G)
    (ad : F.mapDerivedCategory ⊣ G.mapDerivedCategory)
    (h : ∀ M : C,
      ad.unit.app ((DerivedCategory.singleFunctor C 0).obj M) ≫
        G.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).hom.app M) ≫
        (G.mapDerivedCategorySingleFunctor 0).hom.app (F.obj M) =
          (DerivedCategory.singleFunctor C 0).map (adj.unit.app M))
    (M : C) (N : D) (b : F.obj M ⟶ N) :
    ad.homEquiv _ _ ((F.mapDerivedCategorySingleFunctor 0).hom.app M ≫
      (DerivedCategory.singleFunctor D 0).map b) =
      (DerivedCategory.singleFunctor C 0).map (adj.homEquiv _ _ b) ≫
        (G.mapDerivedCategorySingleFunctor 0).inv.app N := by
  rw [Adjunction.homEquiv_unit, Functor.map_comp]
  apply (cancel_mono ((G.mapDerivedCategorySingleFunctor 0).hom.app N)).mp
  simp only [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id, (G.mapDerivedCategorySingleFunctor 0).hom.naturality b]
  have hh := congrArg (fun z ↦ z ≫ (DerivedCategory.singleFunctor C 0).map (G.map b)) (h M)
  simpa only [Category.assoc, Adjunction.homEquiv_unit,
    CategoryTheory.Functor.map_comp, Functor.comp_map] using hh

private theorem comp_single_inv {B : Type*} [Category B] [Abelian B] [HasDerivedCategory B]
    (H : B ⥤ C) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (N : B) :
    ((H ⋙ F).mapDerivedCategorySingleFunctor 0).inv.app N ≫
      (Functor.mapDerivedCategoryCompIso H F).hom.app
        ((DerivedCategory.singleFunctor B 0).obj N) =
      (F.mapDerivedCategorySingleFunctor 0).inv.app (H.obj N) ≫
        F.mapDerivedCategory.map ((H.mapDerivedCategorySingleFunctor 0).inv.app N) := by
  apply (cancel_mono
    (F.mapDerivedCategory.map ((H.mapDerivedCategorySingleFunctor 0).hom.app N) ≫
      (F.mapDerivedCategorySingleFunctor 0).hom.app (H.obj N))).mp
  simp only [Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor, Iso.inv_hom_id_app]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app]
  rfl


private theorem triple_single_inv
    {B E : Type*} [Category B] [Abelian B] [HasDerivedCategory B]
    [Category E] [Abelian E] [HasDerivedCategory E]
    (H : B ⥤ C) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (J : E ⥤ B) [J.Additive] [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    {M : D} {N : C} {P : B} {Q : E}
    (a : M ⟶ F.obj N) (b : N ⟶ H.obj P) (c : P ⟶ J.obj Q) :
    (DerivedCategory.singleFunctor D 0).map (a ≫ F.map (b ≫ H.map c)) ≫
      (((J ⋙ H) ⋙ F).mapDerivedCategorySingleFunctor 0).inv.app Q ≫
      (Functor.mapDerivedCategoryCompIso (J ⋙ H) F).hom.app
        ((DerivedCategory.singleFunctor E 0).obj Q) ≫
      F.mapDerivedCategory.map ((Functor.mapDerivedCategoryCompIso J H).hom.app
        ((DerivedCategory.singleFunctor E 0).obj Q)) =
    ((DerivedCategory.singleFunctor D 0).map a ≫
      (F.mapDerivedCategorySingleFunctor 0).inv.app N) ≫
    F.mapDerivedCategory.map
      (((DerivedCategory.singleFunctor C 0).map b ≫
        (H.mapDerivedCategorySingleFunctor 0).inv.app P) ≫
        H.mapDerivedCategory.map ((DerivedCategory.singleFunctor B 0).map c ≫
          (J.mapDerivedCategorySingleFunctor 0).inv.app Q)) := by
  rw [reassoc_of% (comp_single_inv F (J ⋙ H) Q)]
  erw [← Functor.map_comp, comp_single_inv H J Q]
  have hF := (F.mapDerivedCategorySingleFunctor 0).inv.naturality (b ≫ H.map c)
  dsimp only [Functor.comp_map] at hF
  erw [Functor.map_comp, Category.assoc, reassoc_of% hF]
  simp only [Functor.map_comp, Category.assoc]
  have hH := (H.mapDerivedCategorySingleFunctor 0).inv.naturality c
  dsimp only [Functor.comp_map] at hH
  have hh := congrArg F.mapDerivedCategory.map hH
  simp only [Functor.map_comp] at hh
  rw [reassoc_of% hh]


private theorem triple_transpose
    {A B C E : Type*} [Category A] [Category B] [Category C] [Category E]
    {F₁ : A ⥤ B} {G₁ : B ⥤ A} {F₂ : B ⥤ C} {G₂ : C ⥤ B}
    {F₃ : C ⥤ E} {G₃ : E ⥤ C}
    (ad₁ : F₁ ⊣ G₁) (ad₂ : F₂ ⊣ G₂) (ad₃ : F₃ ⊣ G₃)
    {X : A} {Y : B} {Z : C} {W : E}
    (a : F₁.obj X ⟶ Y) (b : F₂.obj Y ⟶ Z) (c : F₃.obj Z ⟶ W) :
    ((ad₁.comp ad₂).comp ad₃).homEquiv X W (F₃.map (F₂.map a ≫ b) ≫ c) =
      ad₁.homEquiv X Y a ≫ G₁.map (ad₂.homEquiv Y Z b ≫ G₂.map (ad₃.homEquiv Z W c)) := by
  rw [Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
  change ad₁.homEquiv _ _ (ad₂.homEquiv _ _
    (ad₃.homEquiv _ _ (F₃.map (F₂.map a ≫ b) ≫ c))) = _
  rw [ad₃.homEquiv_naturality_left, Category.assoc,
    ad₂.homEquiv_naturality_left, ad₂.homEquiv_naturality_right,
    ad₁.homEquiv_naturality_right]

section Closure
open AlgebraicGeometry AlgebraicGeometry.ProEtale MonoidalCategory
universe w
variable (X : Scheme.{w})
  {A B : Sheaf (ProEt.topology X) Ab.{w + 1}}
  [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
  (ψ : A ⟶ B) [IsMonHom ψ] [PreservesFiniteLimits (Mod.extendScalars ψ)]

private theorem closure_single_transpose
    (M : Mod _ A) (N : Mod _ B) (b : (Mod.extendScalars ψ).obj M ⟶ N) :
    (Mod.derivedExtendMapDerivedCategoryAdjunction ψ).homEquiv _ _
      ((Mod.extendScalars ψ).singleFunctorCompLeftDerivedFunctorIso.hom.app M ≫
        (DerivedCategory.singleFunctor _ 0).map b) =
      (DerivedCategory.singleFunctor _ 0).map
        ((Mod.extendRestrictAdjunction ψ).homEquiv _ _ b) ≫
          ((Mod.comap ψ).mapDerivedCategorySingleFunctor 0).inv.app N := by
  let ad := (Mod.derivedExtendMapDerivedCategoryAdjunction ψ).ofNatIsoLeft
    (Mod.extendScalars ψ).leftDerivedFunctorIsoMapDerivedCategory
  have hu (K : HomotopyCategory (Mod _ A) (.up ℤ)) :
      ad.unit.app (DerivedCategory.Qh.obj K) ≫
        (Mod.comap ψ).mapDerivedCategory.map
          ((Mod.extendScalars ψ).mapDerivedCategoryFactorsh.hom.app K) ≫
        (Mod.comap ψ).mapDerivedCategoryFactorsh.hom.app
          (((Mod.extendScalars ψ).mapHomotopyCategory (.up ℤ)).obj K) =
      DerivedCategory.Qh.map
        (((Mod.extendRestrictAdjunction ψ).mapHomotopyCategory (.up ℤ)).unit.app K) := by
    dsimp only [ad, Adjunction.ofNatIsoLeft_unit, NatTrans.comp_app,
      Functor.whiskerRight_app]
    simp only [Category.assoc, ← Functor.map_comp_assoc]
    have hf := NatTrans.congr_app
      (Mod.extendScalars ψ).leftDerivedFunctorIsoMapDerivedCategory_hom_fac K
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hf
    rw [hf]
    exact Mod.derivedExtendMapDerivedCategoryAdjunction_unit_app_fac ψ K
  have hs := single_hom_of_unit (Mod.extendScalars ψ) (Mod.comap ψ)
    (Mod.extendRestrictAdjunction ψ) ad
    (exact_single_unit _ _ _ _ (unit_cochain _ _ _ _ hu)) M N b
  simpa only [ad, Adjunction.homEquiv_ofNatIsoLeft_apply,
    Functor.singleFunctorCompLeftDerivedFunctorIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.assoc] using hs

omit [PreservesFiniteLimits (Mod.extendScalars ψ)] in
private theorem closure_regular_isIso :
    IsIso (((Mod.extendRestrictAdjunction ψ).homEquiv _ _).symm (Mod.comapUnitHom ψ)) := by
  let := Mod.extendScalarsOplaxMonoidal ψ
  have hh := Mod.isIso_extendScalarsOplaxMonoidal_η ψ
  change IsIso (Functor.OplaxMonoidal.η (Mod.extendScalars ψ))
  exact hh

private def closureRegularIso :
    (Mod.extendScalars ψ).leftDerivedFunctor.obj
      ((DerivedCategory.singleFunctor _ 0).obj (Mod.regular A)) ≅
        (DerivedCategory.singleFunctor _ 0).obj (Mod.regular B) := by
  let b := ((Mod.extendRestrictAdjunction ψ).homEquiv
    (Mod.regular A) (Mod.regular B)).symm (Mod.comapUnitHom ψ)
  letI : IsIso b := closure_regular_isIso X ψ
  refine ((Mod.extendScalars ψ).singleFunctorCompLeftDerivedFunctorIso.app _) ≪≫ ?_
  change (DerivedCategory.singleFunctor _ 0).obj ((Mod.extendScalars ψ).obj (Mod.regular A)) ≅
    (DerivedCategory.singleFunctor _ 0).obj (Mod.regular B)
  exact (DerivedCategory.singleFunctor _ 0).mapIso (asIso b)

private theorem closureRegularIso_transpose :
    (Mod.derivedExtendMapDerivedCategoryAdjunction ψ).homEquiv _ _
      (closureRegularIso X ψ).hom =
    (DerivedCategory.singleFunctor _ 0).map (Mod.comapUnitHom ψ) ≫
      ((Mod.comap ψ).mapDerivedCategorySingleFunctor 0).inv.app (Mod.regular B) := by
  dsimp only [closureRegularIso, id, Iso.trans_hom, Functor.mapIso_hom, asIso_hom,
    Iso.app_hom]
  rw [closure_single_transpose X ψ, Equiv.apply_symm_apply]
end Closure

variable {X : Scheme.{u}} {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
  (φ : R ⟶ S)
private def regularScalarMap : SheafOfModules.unit ((adicLisseForget X).obj R) ⟶
    (pbcRestrict φ).obj (SheafOfModules.unit ((adicLisseForget X).obj S)) where
  val.app U := ModuleCat.homMk
    ((forget₂ RingCat AddCommGrpCat).map (((adicLisseForget X).map φ).hom.app U))
    (fun r ↦ by
      apply ConcreteCategory.hom_ext
      intro m
      exact (map_mul (φ.hom.app U).hom r m).symm)
  val.naturality := by
    intro U V f
    apply ConcreteCategory.hom_ext
    intro s
    exact ConcreteCategory.congr_hom (φ.hom.naturality f) s

private theorem unitMapTranspose_isIso :
    IsIso (((pbcScalarAdjunction φ).homEquiv _ _).symm (regularScalarMap φ)) := by
  let a := pbcScalarAdjunction φ
  let g := regularScalarMap φ
  apply isIso_of_coyoneda_map_bijective
  intro N
  let E : (SheafOfModules.unit ((adicLisseForget X).obj S) ⟶ N) ≃
      (SheafOfModules.unit ((adicLisseForget X).obj R) ⟶ (pbcRestrict φ).obj N) :=
    N.unitHomEquiv.trans ((pbcRestrict φ).obj N).unitHomEquiv.symm
  have h (f : SheafOfModules.unit ((adicLisseForget X).obj S) ⟶ N) :
      a.homEquiv _ _ (((a.homEquiv _ _).symm g) ≫ f) = E f := by
    rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
    apply ((pbcRestrict φ).obj N).unitHomEquiv.injective
    change ((pbcRestrict φ).obj N).unitHomEquiv (g ≫ (pbcRestrict φ).map f) =
      ((pbcRestrict φ).obj N).unitHomEquiv
        (((pbcRestrict φ).obj N).unitHomEquiv.symm (N.unitHomEquiv f))
    rw [Equiv.apply_symm_apply]
    ext U
    change f.val.app U (φ.hom.app U (1 : R.obj.obj U)) = f.val.app U (1 : S.obj.obj U)
    rw [map_one]
  apply Function.Bijective.of_comp_left (f := a.homEquiv _ _) _ (a.homEquiv _ _).injective
  convert E.bijective using 1
  funext f
  exact h f

private theorem normalizedHom
    (P : CochainComplex (pbcModules X R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology X) (R := R) P)
    (K : CochainComplex (pbcModules X S) ℤ)
    (a : ((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P ⟶ K) :
    (pbcDerivedScalarAdjunction φ).homEquiv _ _
        (pbcComplexCounit φ P ≫ DerivedCategory.Q.map a) =
      DerivedCategory.Q.map
        (((pbcScalarAdjunction φ).mapHomologicalComplex (.up ℤ)).homEquiv P K a) ≫
          (pbcRestrict φ).mapDerivedCategoryFactors.inv.app K := by
  have hu := (pbcDerivedScalarAdjunction_exists φ).exists.choose_spec P hP
  rw [Adjunction.homEquiv_unit, Functor.map_comp]
  apply (cancel_mono ((pbcRestrict φ).mapDerivedCategoryFactors.hom.app K)).mp
  dsimp only [pbcDerivedRestrict]
  simp only [Category.assoc]
  erw [(pbcRestrict φ).mapDerivedCategoryFactors_hom_naturality a]
  have hh := congrArg (fun z ↦ z ≫ DerivedCategory.Q.map
    (((pbcRestrict φ).mapHomologicalComplex (.up ℤ)).map a)) hu
  have he : ((pbcScalarAdjunction φ).mapHomologicalComplex (.up ℤ)).unit.app P =
      (NatTrans.mapHomologicalComplex (pbcScalarAdjunction φ).unit (.up ℤ)).app P := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact Adjunction.mapHomologicalComplex_unit_app_f _ _ _ _
  dsimp only [Functor.comp_obj, Functor.id_obj] at *
  simp only [Iso.inv_hom_id_app]
  rw [Adjunction.homEquiv_unit, he]
  erw [Category.comp_id]
  simpa only [pbcDerivedScalarAdjunction, pbcDerivedRestrict, Category.assoc,
    CategoryTheory.Functor.map_comp, Functor.comp_map] using hh

private theorem regular_single_kFlat :
    CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology X) (R := R)
      ((CochainComplex.singleFunctor _ 0).obj
        (SheafOfModules.unit ((adicLisseForget X).obj R))) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  intro F hF i
  exact (quasiIsoAt_iff_exactAt' (HomologicalComplex.rightUnitor F).hom i (hF i)).1
    inferInstance

private def singleComparison (M : pbcModules X R) :
    (pbcDerivedExtend φ).obj ((DerivedCategory.singleFunctor _ 0).obj M) ⟶
      (DerivedCategory.singleFunctor _ 0).obj ((pbcExtend φ).obj M) :=
  pbcComplexCounit φ ((CochainComplex.singleFunctor _ 0).obj M) ≫
    DerivedCategory.Q.map (((pbcExtend φ).mapCochainComplexSingleFunctor 0).hom.app M)

private theorem singleComparison_transpose (M : pbcModules X R) (N : pbcModules X S)
    (hM : CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology X) (R := R)
      ((CochainComplex.singleFunctor _ 0).obj M))
    (b : (pbcExtend φ).obj M ⟶ N) :
    (pbcDerivedScalarAdjunction φ).homEquiv _ _
      (singleComparison φ M ≫ (DerivedCategory.singleFunctor _ 0).map b) =
      (DerivedCategory.singleFunctor _ 0).map ((pbcScalarAdjunction φ).homEquiv _ _ b) ≫
        ((pbcRestrict φ).mapDerivedCategorySingleFunctor 0).inv.app N := by
  unfold singleComparison
  rw [Category.assoc]
  change (pbcDerivedScalarAdjunction φ).homEquiv _ _
    ((pbcComplexCounit φ _) ≫ DerivedCategory.Q.map _ ≫
      DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map b)) = _
  rw [← Functor.map_comp]
  erw [normalizedHom φ _ hM]
  rw [← cancel_mono ((pbcRestrict φ).mapDerivedCategoryFactors.hom.app
    ((CochainComplex.singleFunctor _ 0).obj N))]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id,
    (pbcRestrict φ).mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app N]
  change DerivedCategory.Q.map _ =
    DerivedCategory.Q.map ((CochainComplex.singleFunctor (pbcModules X R) 0).map
      ((pbcScalarAdjunction φ).homEquiv _ _ b)) ≫ DerivedCategory.Q.map _
  rw [← Functor.map_comp]
  congr 1
  apply HomologicalComplex.Hom.ext
  funext q
  by_cases hq : q = 0
  · subst q
    simp only [Functor.mapHomologicalComplex_obj_X, HomologicalComplex.comp_f]
    change (pbcScalarAdjunction φ).unit.app M ≫
      (pbcRestrict φ).map (𝟙 ((pbcExtend φ).obj M)) ≫ (pbcRestrict φ).map b =
        (pbcScalarAdjunction φ).unit.app M ≫ (pbcRestrict φ).map b ≫
          (pbcRestrict φ).map (𝟙 N)
    dsimp only [Functor.comp_obj, Functor.id_obj]
    simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  · apply (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M q hq).eq_of_src

private theorem singleComparison_isIso :
    IsIso (singleComparison φ (SheafOfModules.unit ((adicLisseForget X).obj R))) := by
  have := pbcExtensionCounit_isIso φ _ (regular_single_kFlat (R := R))
  have : IsIso (pbcComplexCounit φ ((CochainComplex.singleFunctor _ 0).obj
      (SheafOfModules.unit ((adicLisseForget X).obj R)))) := by
    unfold pbcComplexCounit
    infer_instance
  unfold singleComparison
  infer_instance

private def derivedRegularIso :
    (pbcDerivedExtend φ).obj ((DerivedCategory.singleFunctor _ 0).obj
      (SheafOfModules.unit ((adicLisseForget X).obj R))) ≅
        (DerivedCategory.singleFunctor _ 0).obj
          (SheafOfModules.unit ((adicLisseForget X).obj S)) := by
  let g := ((pbcScalarAdjunction φ).homEquiv _ _).symm (regularScalarMap φ)
  letI := unitMapTranspose_isIso φ
  letI := singleComparison_isIso φ
  exact asIso (singleComparison φ _ ≫ (DerivedCategory.singleFunctor _ 0).map g)

private theorem derivedRegularIso_transpose :
    (pbcDerivedScalarAdjunction φ).homEquiv _ _ (derivedRegularIso φ).hom =
      (DerivedCategory.singleFunctor _ 0).map (regularScalarMap φ) ≫
        ((pbcRestrict φ).mapDerivedCategorySingleFunctor 0).inv.app
          (SheafOfModules.unit ((adicLisseForget X).obj S)) := by
  dsimp only [derivedRegularIso, asIso_hom]
  rw [singleComparison_transpose φ _ _ (regular_single_kFlat (R := R)),
    Equiv.apply_symm_apply]

end RegularRealizationProof

namespace WeilConjectures.CondensedExceptionalReconstruction
open CondensedERealization CompactSupportCondensedRealization PurityFiniteSetting
open RegularRealizationProof
variable (l : ℕ) [Fact l.Prime] (k : Type u) [_root_.Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
attribute [local instance] CondensedERealization.At.encodingAdditive
  CondensedERealization.At.encodingInverseAdditive
attribute [local irreducible] WeilConjectures.purCoefficientModel

private theorem regular_integral (T : Base k) :
    PbcIsBoundedConstructibleComplete T.scheme (pbcIntegralDatum l (Field.{u} l))
      (regular l k T) := by
  have htop : IsUnit (l : Γ(T.scheme, ⊤)) := by
    apply T.scheme.toRingedSpace.isUnit_of_isUnit_germ ⊤ (l : Γ(T.scheme, ⊤))
    intro x _
    simpa only [map_natCast] using base_primeUnit l k T x
  apply (purCoefficientModel_bounded_predicate l (Field.{u} l) T.scheme
    (base_dimension k T) htop _).mpr
  let e : (purCoefficientModel l (Field.{u} l) T.scheme).functor.obj (regular l k T) ≅
      integralConstantCoefficientObject l (Field.{u} l) T.scheme := by
    unfold purCoefficientModel
    exact ((purOrdinaryCoefficientModel l (Field.{u} l) T.scheme).mapDerivedCategorySingleFunctor
      0).app _ ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso
        (CondensedRing.ringModuleUnitIso T.scheme
          ((adicLisseForget T.scheme).mapIso
            (purCoefficientIso l (Field.{u} l) T.scheme).symm))
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (l + 1)
  let : Fact p.Prime := ⟨hprime⟩
  let D₀ : FiniteFieldDatum.{0} :=
    { p := p
      a := 1
      q := p
      prime := hprime
      exponent_pos := le_rfl
      cardinality_eq := (pow_one p).symm
      k₀ := ZMod p
      card_base := by simp [Nat.card_eq_fintype_card]
      k := AlgebraicClosure (ZMod p) }
  have hl₀ : l ≠ D₀.p := by change l ≠ p; omega
  exact (sfIntegralConstructible l (Field.{u} l) T.scheme).prop_of_iso e.symm
    (integralConstantCoefficient_constructible l (Field.{u} l) T.scheme D₀ hl₀).2.1

private theorem integral_shift_closed (T : Base k) : IntegralShiftClosed l k T := by
  let h := (pbcIntegralUniformComplete_isTriangulated l (Field.{u} l) T.scheme
    (base_dimension k T) (base_primeUnit l k T)).2
  let := h
  intro K n
  exact ObjectProperty.le_shift
    (PbcIsBoundedConstructibleComplete T.scheme (pbcIntegralDatum l (Field.{u} l)))
    n K.obj K.property

private def modelComparison (D : CondensedERealization.Data l (Field.{u} l) k)
    (T : Base k) :
    ObjectProperty.ι (PbcIsBoundedConstructibleComplete T.scheme
        (pbcIntegralDatum l (Field.{u} l))) ⋙ normalizationModel l k D T ≅
      realization l k D T ⋙
        (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj l) T.scheme)).ι :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerRight (D.atObject T).scalarExtension.symm
      (moduleEncoding l (Field.{u} l) T.scheme
        (D.atObject T).sectionIso).mapDerivedCategory.inverse ≪≫
      Functor.isoWhiskerLeft
        (pbcRationalization T.scheme (pbcIntegralDatum l (Field.{u} l))
          (pbcUniformizer l (Field.{u} l)) ⋙ (D.atObject T).realization.functor ⋙
            (boundedConstructible (Coefficient (Field.{u} l) T.scheme)).ι)
        (moduleEncoding l (Field.{u} l) T.scheme
          (D.atObject T).sectionIso).mapDerivedCategory.unitIso.symm)
    (omegaScalar l (Field.{u} l) (embedding l) T.scheme)

private def normalizedShifts (D : CondensedERealization.Data l (Field.{u} l) k)
    (T : Base k) (h : IntegralShiftClosed l k T) (n : ℤ) :
    integralShift l k T h n ⋙ realization l k D T ⋙
        (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj l) T.scheme)).ι ≅
      realization l k D T ⋙
        (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj l) T.scheme)).ι ⋙
          shiftFunctor _ n :=
  Functor.isoWhiskerLeft (integralShift l k T h n) (modelComparison l k D T).symm ≪≫
    Functor.isoWhiskerLeft
      (ObjectProperty.ι (PbcIsBoundedConstructibleComplete T.scheme
        (pbcIntegralDatum l (Field.{u} l))))
      ((normalizationModel l k D T).commShiftIso n) ≪≫
    Functor.isoWhiskerRight (modelComparison l k D T) (shiftFunctor _ n)

private def encodingRegularIso (D : CondensedERealization.Data l (Field.{u} l) k)
    (T : Base k) :
    (moduleEncoding l (Field.{u} l) T.scheme (D.atObject T).sectionIso).functor.obj
      (Mod.regular (Coefficient (Field.{u} l) T.scheme)) ≅
        SheafOfModules.unit ((adicLisseForget T.scheme).obj
          (rationalCoefficientSheaf l T.scheme (Field.{u} l))) :=
  (CondensedRing.ringModuleEquivalenceOfIso T.scheme
    ((adicLisseForget T.scheme).mapIso (D.atObject T).sectionIso).symm).functor.mapIso
      (CondensedRing.sectionModuleRegularIso T.scheme (Coefficient (Field.{u} l) T.scheme)) ≪≫
    CondensedRing.ringModuleUnitIso T.scheme
      ((adicLisseForget T.scheme).mapIso (D.atObject T).sectionIso).symm

private def coefficientSectionMap (D : CondensedERealization.Data l (Field.{u} l) k)
    (T : Base k) : normalizationRegular l k T ⟶
      (normalizationOrdinaryRestriction l k D T).obj
        (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj l) T.scheme)) := by
  let φ := normalizationScalarMap l k D T
  let a : normalizationRegular l k T ⟶
      (pbcRestrict φ).obj (SheafOfModules.unit
        ((adicLisseForget T.scheme).obj (rationalCoefficientSheaf l T.scheme (Field.{u} l)))) :=
    { val.app V := ModuleCat.homMk
        ((forget₂ RingCat AddCommGrpCat).map (((adicLisseForget T.scheme).map φ).hom.app V))
        (fun r ↦ by
          apply ConcreteCategory.hom_ext
          intro m
          exact (map_mul (φ.hom.app V).hom r m).symm)
      val.naturality := by
        intro U V f
        apply ConcreteCategory.hom_ext
        intro s
        exact ConcreteCategory.congr_hom (φ.hom.naturality f) s }
  exact a ≫ (pbcRestrict φ).map ((encodingRegularIso l k D T).inv ≫
    (moduleEncoding l (Field.{u} l) T.scheme (D.atObject T).sectionIso).functor.map
      (Mod.comapUnitHom (C := Sheaf (ProEt.topology T.scheme) Ab.{u + 1})
        (coefficientMap (omegaMap l (Field.{u} l) (embedding l)) T.scheme)))

private theorem coefficientSectionMap_normalized
    (D : CondensedERealization.Data l (Field.{u} l) k) (T : Base k) :
    IsCoefficientInclusion l k D T (coefficientSectionMap l k D T) := by
  intro V s
  rfl

private def encodingDerivedRegularIso
    (D : CondensedERealization.Data l (Field.{u} l) k) (T : Base k) :
    (moduleEncoding l (Field.{u} l) T.scheme
      (D.atObject T).sectionIso).mapDerivedCategory.inverse.obj
      ((DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit
        ((adicLisseForget T.scheme).obj (rationalCoefficientSheaf l T.scheme (Field.{u} l))))) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        (Mod.regular (Coefficient (Field.{u} l) T.scheme)) := by
  let e := moduleEncoding l (Field.{u} l) T.scheme (D.atObject T).sectionIso
  let a := (DerivedCategory.singleFunctor _ 0).map (encodingRegularIso l k D T).inv ≫
    (e.functor.mapDerivedCategorySingleFunctor 0).inv.app _
  have : IsIso ((e.mapDerivedCategory.symm.toAdjunction.homEquiv _ _).symm a) := by
    rw [Adjunction.homEquiv_counit]
    infer_instance
  exact asIso ((e.mapDerivedCategory.symm.toAdjunction.homEquiv _ _).symm a)

private theorem encodingDerivedRegularIso_transpose
    (D : CondensedERealization.Data l (Field.{u} l) k) (T : Base k) :
    ((moduleEncoding l (Field.{u} l) T.scheme
      (D.atObject T).sectionIso).mapDerivedCategory.symm.toAdjunction).homEquiv _ _
        (encodingDerivedRegularIso l k D T).hom =
      (DerivedCategory.singleFunctor _ 0).map (encodingRegularIso l k D T).inv ≫
        ((moduleEncoding l (Field.{u} l) T.scheme
          (D.atObject T).sectionIso).functor.mapDerivedCategorySingleFunctor 0).inv.app _ := by
  exact Equiv.apply_symm_apply _ _

private def normalizedRegularIso
    (D : CondensedERealization.Data l (Field.{u} l) k) (T : Base k) :
    (normalizationModel l k D T).obj (regular l k T) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj l) T.scheme)) := by
  letI : PreservesFiniteLimits (Mod.extendScalars
      (coefficientMap (omegaMap l (Field.{u} l) (embedding l)) T.scheme)) :=
    omegaExtension_flat l (Field.{u} l) (embedding l) T.scheme
  exact (omegaScalar l (Field.{u} l) (embedding l) T.scheme).mapIso
    (((moduleEncoding l (Field.{u} l) T.scheme
      (D.atObject T).sectionIso).mapDerivedCategory.inverse.mapIso
        (derivedRegularIso (normalizationScalarMap l k D T))) ≪≫
          encodingDerivedRegularIso l k D T) ≪≫
    closureRegularIso T.scheme
      (coefficientMap (omegaMap l (Field.{u} l) (embedding l)) T.scheme)

set_option maxHeartbeats 2000000 in
-- The three fixed derived categories make the comparison and naturality elaboration expensive.
attribute [local irreducible] _root_.DerivedCategory _root_.instCategoryDerivedCategory in
private theorem derivedInclusion_factor
    (D : CondensedERealization.Data l (Field.{u} l) k) (T : Base k) :
    normalizationDerivedInclusion l k D T (coefficientSectionMap l k D T) =
      ((DerivedCategory.singleFunctor _ 0).map
        (regularScalarMap (normalizationScalarMap l k D T)) ≫
        ((pbcRestrict
          (normalizationScalarMap l k D T)).mapDerivedCategorySingleFunctor 0).inv.app _) ≫
      (pbcDerivedRestrict (normalizationScalarMap l k D T)).map
        (((DerivedCategory.singleFunctor _ 0).map (encodingRegularIso l k D T).inv ≫
          ((moduleEncoding l (Field.{u} l) T.scheme
          (D.atObject T).sectionIso).functor.mapDerivedCategorySingleFunctor 0).inv.app _) ≫
          (moduleEncoding l (Field.{u} l) T.scheme
            (D.atObject T).sectionIso).mapDerivedCategory.functor.map
              ((DerivedCategory.singleFunctor _ 0).map
                (Mod.comapUnitHom (C := Sheaf (ProEt.topology T.scheme) Ab.{u + 1})
                (coefficientMap (omegaMap l (Field.{u} l) (embedding l)) T.scheme)) ≫
                ((Mod.comap (D := Sheaf (ProEt.topology T.scheme) Ab.{u + 1})
                  (coefficientMap (omegaMap l (Field.{u} l) (embedding l))
                  T.scheme)).mapDerivedCategorySingleFunctor 0).inv.app
                    (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj l)
                      T.scheme)))) := by
  dsimp only [normalizationDerivedInclusion, normalizationRestrictionComparison,
    Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app]
  exact triple_single_inv
    (pbcRestrict (normalizationScalarMap l k D T))
    (moduleEncoding l (Field.{u} l) T.scheme (D.atObject T).sectionIso).functor
    (Mod.comap (D := Sheaf (ProEt.topology T.scheme) Ab.{u + 1})
      (coefficientMap (omegaMap l (Field.{u} l) (embedding l)) T.scheme))
    (regularScalarMap (normalizationScalarMap l k D T))
    (encodingRegularIso l k D T).inv
    (Mod.comapUnitHom (C := Sheaf (ProEt.topology T.scheme) Ab.{u + 1})
      (coefficientMap (omegaMap l (Field.{u} l) (embedding l)) T.scheme))

section NormalizedUnitComposition
attribute [local irreducible] derivedRegularIso encodingDerivedRegularIso
set_option maxHeartbeats 2000000 in
-- Composing the three normalized adjunctions requires elaborating their large fixed categories.
attribute [local irreducible] pbcDerivedScalarAdjunction
  _root_.DerivedCategory _root_.instCategoryDerivedCategory in
private theorem normalizedRegularIso_transpose
    (D : CondensedERealization.Data l (Field.{u} l) k) (T : Base k) :
    (normalizationAdjunction l k D T).homEquiv _ _ (normalizedRegularIso l k D T).hom =
      normalizationDerivedInclusion l k D T (coefficientSectionMap l k D T) := by
  let : PreservesFiniteLimits (Mod.extendScalars
      (coefficientMap (omegaMap l (Field.{u} l) (embedding l)) T.scheme)) :=
    omegaExtension_flat l (Field.{u} l) (embedding l) T.scheme
  refine (triple_transpose
    (pbcDerivedScalarAdjunction (normalizationScalarMap l k D T))
    (moduleEncoding l (Field.{u} l) T.scheme
      (D.atObject T).sectionIso).mapDerivedCategory.symm.toAdjunction
    (Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap (omegaMap l (Field.{u} l) (embedding l)) T.scheme))
    (derivedRegularIso (normalizationScalarMap l k D T)).hom
    (encodingDerivedRegularIso l k D T).hom
    (closureRegularIso T.scheme
      (coefficientMap (omegaMap l (Field.{u} l) (embedding l)) T.scheme)).hom).trans ?_
  rw [derivedRegularIso_transpose, encodingDerivedRegularIso_transpose,
    closureRegularIso_transpose]
  exact (derivedInclusion_factor l k D T).symm

end NormalizedUnitComposition

/-- The regular coefficient, scalar unit and all integer shifts have the exact normalized
properties required by RealizationProperties.
Source: blueprint sk-prop-sp-integral-adjunction and sk-prop-sp-rational, scalar
extension construction; parent reconstruction proof Step 7.
(blueprint: lem-pur-condensed-exceptional-realization-properties).

Proof: the completed rank-one coefficient has constant rank-one reductions with their
quotient cocycle and invertible completion unit, hence is bounded constructible complete.
K-flat shifts preserve the common finite cohomological interval and etale origins, and
the derived inverse limit commutes with these shifts. Define the section map by the
completed coefficient map followed by section encoding and closure inclusion. Its
normalized transpose is multiplication B tensor_A A to B, with inverse b tensor 1.
Flatness and exact coefficient encoding preserve this isomorphism in the derived
categories. The natural comparison between scalar extension and the recorded realization,
whiskered by shifts and the canonical commShiftIso, has precisely the required
component formula. -/
theorem condensed_exceptional_realization_properties
    (D : CondensedERealization.Data l (Field.{u} l) k) :
    Nonempty (RealizationProperties l k D) := by
  refine ⟨{
    regular_mem := regular_integral l k
    coefficientInclusion := coefficientSectionMap l k D
    coefficientInclusion_normalized := coefficientSectionMap_normalized l k D
    coefficientUnit := fun T ↦
      (normalizationComparison l k D T ⟨regular l k T, regular_integral l k T⟩).symm ≪≫
        normalizedRegularIso l k D T
    coefficientUnit_normalized := ?_
    shiftClosed := integral_shift_closed l k
    shifts := fun T n ↦ normalizedShifts l k D T (integral_shift_closed l k T) n
    shifts_normalized := ?_ }⟩
  · intro T
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]
    exact normalizedRegularIso_transpose l k D T
  · intro T n K
    rfl

end WeilConjectures.CondensedExceptionalReconstruction
