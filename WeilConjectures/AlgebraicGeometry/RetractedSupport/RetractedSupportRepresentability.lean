/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RetractedSupport.RetractedSupportLocalizationComparison
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedExteriorProduct
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import WeilConjectures.Algebra.Homology.DerivedFreeModuleHomology
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedBelowProEtaleComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.Supported.ProEtaleSupportedExteriorProduct
public import WeilConjectures.AlgebraicGeometry.Support.SupportSiteComparison
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedCoefficientDerivedOpenMate
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.UnitShift

/-! # Representability of the supported-section inclusion on etale inputs

Source: the supported-Hom identification in the latest blueprint's proof of
`lem-pur-gysin-structure` (blueprint: lem-pur-retracted-support-representability).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.RetractedSupport

variable (P : WeilConjectures.PurityFiniteSetting.{u})
  {X Y : Scheme.{u}} (s : Y ⟶ X) [IsClosedImmersion s]

private theorem natIso_hom_inv_apply {C : Type*} [Category C]
    {F G : C ⥤ Type v} (e : F ≅ G) (B : C) (x : F.obj B) :
    e.inv.app B (e.hom.app B x) = x := by
  have h := ConcreteCategory.congr_hom (congr_app e.hom_inv_id B) x
  exact h

private theorem natIso_inv_hom_apply {C : Type*} [Category C]
    {F G : C ⥤ Type v} (e : F ≅ G) (B : C) (x : G.obj B) :
    e.hom.app B (e.inv.app B x) = x := by
  have h := ConcreteCategory.congr_hom (congr_app e.inv_hom_id B) x
  exact h

private noncomputable def freeModuleRepresentation
    (A : Type (u + 1)) [CommRing A] :
    DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) 0 ⋙
        forget (ModuleCat.{u + 1} A) ≅
      coyoneda.obj (op ((DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) 0).obj
        (ModuleCat.of A A))) := by
  let e := (AlgebraicGeometry.derivedFreeModule_hom_homology A).choose
  have he := (AlgebraicGeometry.derivedFreeModule_hom_homology A).choose_spec
  exact (NatIso.ofComponents (fun K ↦ (e K).toEquiv.toIso)
    (by
      intro K L f
      ext g
      exact he K L f g)).symm

private noncomputable def adjointRepresentation
    (A : Type (u + 1)) [CommRing A]
    {C : Type*} [Category.{u + 1} C] [HasShift C ℤ]
    (L : DerivedCategory (ModuleCat.{u + 1} A) ⥤ C)
    (R : C ⥤ DerivedCategory (ModuleCat.{u + 1} A)) [R.CommShift ℤ]
    (adj : L ⊣ R) (q : ℤ) :
    R ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) q ⋙
        forget (ModuleCat.{u + 1} A) ≅
      shiftFunctor C q ⋙ coyoneda.obj
        (op (L.obj ((DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) 0).obj
          (ModuleCat.of A A)))) := by
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) 0
  let U := forget (ModuleCat.{u + 1} A)
  let M := (DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) 0).obj
    (ModuleCat.of A A)
  let e : R ⋙ coyoneda.obj (op M) ≅ coyoneda.obj (op (L.obj M)) :=
    NatIso.ofComponents (fun K ↦ (adj.homEquiv M K).symm.toIso)
      (by
        intro K K' f
        ext g
        exact adj.homEquiv_naturality_right_symm g f)
  exact Functor.isoWhiskerLeft R
      (Functor.isoWhiskerRight (H.shiftIso q 0 q (add_zero q)).symm U) ≪≫
    Functor.isoWhiskerRight (R.commShiftIso q).symm (H ⋙ U) ≪≫
    Functor.isoWhiskerLeft (shiftFunctor C q)
      (Functor.isoWhiskerLeft R (freeModuleRepresentation A) ≪≫ e)

private theorem rightDerivedNatTrans_commShift
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    {F G : C ⥤ D} [F.Additive] [G.Additive] (τ : F ⟶ G) :
    NatTrans.CommShift (Functor.rightDerivedFunctorNatTrans τ) ℤ := by
  have he := Functor.rightDerivedNatTrans_fac F.rightDerivedFunctor G.rightDerivedFunctor
    F.rightDerivedFunctorUnit G.rightDerivedFunctorUnit
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
    (Functor.whiskerRight (NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ))
      DerivedCategory.Qh)
  have : NatTrans.CommShift (F.rightDerivedFunctorUnit ≫
      Functor.whiskerLeft DerivedCategory.Qh (Functor.rightDerivedFunctorNatTrans τ)) ℤ := by
    change NatTrans.CommShift (_ ≫ Functor.whiskerLeft _
      (Functor.rightDerivedNatTrans _ _ _ _ _ _)) ℤ
    rw [he]
    infer_instance
  have : IsIso (Functor.whiskerLeft
      (ObjectProperty.ι (HomotopyCategory.subcategoryAcyclic C).rightOrthogonal)
      F.rightDerivedFunctorUnit) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro K
    exact (HomotopyCategory.KInjectives.localizerMorphism_derives
      (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)).isIso_of_isRightDerivedFunctor
      F.rightDerivedFunctorUnit K
  exact NatTrans.CommShift.of_comp_whiskerLeft_Qh F.rightDerivedFunctorUnit _

private theorem rightDerivedPullback_identity
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    {F G : C ⥤ D} [F.Additive] [G.Additive] (τ : F ⟶ G) :
    Functor.rightDerivedPullback (𝟭 C) τ ≫
        Functor.whiskerRight (Functor.mapDerivedCategoryIdIso C).hom
          G.rightDerivedFunctor = Functor.rightDerivedFunctorNatTrans τ := by
  apply Functor.rightDerived_ext F.rightDerivedFunctor F.rightDerivedFunctorUnit
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
  ext K : 2
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  simp only [Functor.whiskerLeft_comp, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]
  rw [Functor.rightDerivedPullback_fac_app_assoc]
  rw [← G.rightDerivedFunctor.map_comp,
    Functor.mapDerivedCategoryIdIso_hom_app_Qh_obj, Iso.inv_hom_id_app]
  erw [G.rightDerivedFunctor.map_id, Category.comp_id]
  symm
  exact congr_app (Functor.rightDerivedNatTrans_fac F.rightDerivedFunctor
    G.rightDerivedFunctor F.rightDerivedFunctorUnit G.rightDerivedFunctorUnit
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
    (Functor.whiskerRight (NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ))
      DerivedCategory.Qh)) ((HomotopyCategory.quotient _ _).obj K)

private theorem derivedTranspose_naturality
    {B C : Type*} [Category B] [Category C] [Abelian B] [Abelian C]
    [HasDerivedCategory B] [HasDerivedCategory C]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    {F F' : B ⥤ C} {G G' : C ⥤ B}
    [F.Additive] [F'.Additive] [G.Additive] [G'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    (a : F ⊣ G) (a' : F' ⊣ G') (ρ : F' ⟶ F) (τ : G ⟶ G')
    (hρ : ∀ M K (f : F.obj M ⟶ K),
      a'.homEquiv M K (ρ.app M ≫ f) = a.homEquiv M K f ≫ τ.app K)
    (M : DerivedCategory B) (K : DerivedCategory C)
    (f : F.mapDerivedCategory.obj M ⟶ K) :
    a'.mapDerivedCategoryRightDerivedAdjunction.homEquiv M K
        ((Functor.exactDerivedMap ρ).app M ≫ f) =
      a.mapDerivedCategoryRightDerivedAdjunction.homEquiv M K f ≫
        (Functor.rightDerivedFunctorNatTrans τ).app K := by
  let aD := a.mapDerivedCategoryRightDerivedAdjunction
  let aD' := a'.mapDerivedCategoryRightDerivedAdjunction
  let I := (𝟭 C).mapDerivedCategory
  let β := Functor.rightDerivedPullback (𝟭 C) τ
  let m := AlgebraicGeometry.Etale.supportCoefficientMate aD aD' I β
  have hm : AlgebraicGeometry.Etale.supportCoefficientMate a a' (𝟭 C) τ = ρ := by
    ext N
    apply (a'.homEquiv N (F.obj N)).injective
    have hu := AlgebraicGeometry.Etale.supportMate_unit a a' (𝟭 C) τ N
    exact hu.trans (by
      simpa only [Category.comp_id, Adjunction.homEquiv_id] using
        (hρ N (F.obj N) (𝟙 _)).symm)
  have hd := AlgebraicGeometry.Etale.derivedMate_eq a a' (𝟭 C) τ
  rw [hm] at hd
  have hi := congr_app (Functor.mapDerivedCategoryCompIso_comp_id F) M
  have hid : (Functor.exactDerivedMap ρ).app M ≫ f =
      m.app M ≫ I.map f ≫ (Functor.mapDerivedCategoryIdIso C).hom.app K := by
    dsimp only [m]
    rw [hd]
    simp only [NatTrans.comp_app, Category.assoc]
    have hn := (Functor.mapDerivedCategoryIdIso C).hom.naturality f
    change I.map f ≫ (Functor.mapDerivedCategoryIdIso C).hom.app K =
      (Functor.mapDerivedCategoryIdIso C).hom.app _ ≫ f at hn
    rw [hn]
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, NatTrans.id_app] at hi
    erw [← Category.assoc ((F.mapDerivedCategoryCompIso (𝟭 C)).hom.app M),
      hi, Category.id_comp]
  rw [hid, ← Category.assoc, aD'.homEquiv_naturality_right]
  rw [AlgebraicGeometry.Etale.coefficientMate_transpose aD aD' I β]
  simp only [Category.assoc]
  exact congrArg (fun t ↦ aD.homEquiv M K f ≫ t)
    (congr_app (rightDerivedPullback_identity τ) K)

private theorem adjointRepresentation_naturality
    (A : Type (u + 1)) [CommRing A]
    {C : Type*} [Category.{u + 1} C] [HasShift C ℤ]
    {L L' : DerivedCategory (ModuleCat.{u + 1} A) ⥤ C}
    {R R' : C ⥤ DerivedCategory (ModuleCat.{u + 1} A)}
    [R.CommShift ℤ] [R'.CommShift ℤ]
    (a : L ⊣ R) (a' : L' ⊣ R')
    (τ : R ⟶ R') [NatTrans.CommShift τ ℤ]
    (ρ : L' ⟶ L)
    (hρ : ∀ M K (f : L.obj M ⟶ K),
      a'.homEquiv M K (ρ.app M ≫ f) = a.homEquiv M K f ≫ τ.app K)
    (q : ℤ) (K : C)
    (f : L.obj ((DerivedCategory.singleFunctor (ModuleCat.{u + 1} A) 0).obj
        (ModuleCat.of A A)) ⟶ K⟦q⟧) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) q).map (τ.app K)
        ((adjointRepresentation A L R a q).inv.app K f) =
      (adjointRepresentation A L' R' a' q).inv.app K
        (ρ.app _ ≫ f) := by
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) 0
  let U := forget (ModuleCat.{u + 1} A)
  let e := freeModuleRepresentation A
  let g := a.homEquiv _ _ f
  have he := e.inv.naturality (τ.app (K⟦q⟧))
  have hs := NatTrans.shift_app_comm τ q K
  have hh := (H.shiftIso q 0 q (add_zero q)).hom.naturality (τ.app K)
  change (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) q).map (τ.app K)
      ((H.shiftIso q 0 q (add_zero q)).hom.app (R.obj K)
        (H.map ((R.commShiftIso q).hom.app K)
          (e.inv.app (R.obj (K⟦q⟧)) g))) =
    (H.shiftIso q 0 q (add_zero q)).hom.app (R'.obj K)
      (H.map ((R'.commShiftIso q).hom.app K)
        (e.inv.app (R'.obj (K⟦q⟧)) (a'.homEquiv _ _ (ρ.app _ ≫ f))))
  rw [hρ]
  have he' := ConcreteCategory.congr_hom he g
  change e.inv.app (R'.obj (K⟦q⟧)) (g ≫ τ.app (K⟦q⟧)) =
    H.map (τ.app (K⟦q⟧)) (e.inv.app (R.obj (K⟦q⟧)) g) at he'
  rw [he']
  have hs' := ConcreteCategory.congr_hom (congrArg H.map hs)
    (e.inv.app (R.obj (K⟦q⟧)) g)
  simp only [Functor.map_comp, ModuleCat.comp_apply] at hs'
  exact (ConcreteCategory.congr_hom hh
    (H.map ((R.commShiftIso q).hom.app K)
      (e.inv.app (R.obj (K⟦q⟧)) g))).symm.trans
        (congrArg (fun z ↦ (H.shiftIso q 0 q (add_zero q)).hom.app (R'.obj K) z) hs')

private theorem exactMap_fac_Q
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (α : F ⟶ G) (K : CochainComplex C ℤ) :
    (Functor.exactDerivedMap α).app (DerivedCategory.Q.obj K) ≫
        G.mapDerivedCategoryFactors.hom.app K =
      F.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex α (.up ℤ)).app K) := by
  have h := AlgebraicGeometry.Etale.exactMap_fac α
    ((HomotopyCategory.quotient C (.up ℤ)).obj K)
  have hf (L : C ⥤ D) [L.Additive]
      [PreservesFiniteLimits L] [PreservesFiniteColimits L] :
      L.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient C (.up ℤ)).obj K) =
        L.mapDerivedCategoryFactors.hom.app K := by
    rw [Functor.mapDerivedCategoryFactorsh_hom_app]
    change L.mapDerivedCategory.map (𝟙 _) ≫ L.mapDerivedCategoryFactors.hom.app K ≫
      𝟙 _ ≫ DerivedCategory.Qh.map (𝟙 _) = _
    simp only [CategoryTheory.Functor.map_id, Category.id_comp]
    erw [Category.comp_id]
  rw [hf, hf] at h
  exact h

private theorem exactMap_single
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (α : F ⟶ G) (M : C) :
    (Functor.exactDerivedMap α).app ((DerivedCategory.singleFunctor C 0).obj M) ≫
        (G.mapDerivedCategorySingleFunctor 0).hom.app M =
      (F.mapDerivedCategorySingleFunctor 0).hom.app M ≫
        (DerivedCategory.singleFunctor D 0).map (α.app M) := by
  have hs (L : C ⥤ D) [L.Additive]
      [PreservesFiniteLimits L] [PreservesFiniteColimits L] :
      (L.mapDerivedCategorySingleFunctor 0).hom.app M =
        L.mapDerivedCategoryFactors.hom.app
          ((HomologicalComplex.single C (.up ℤ) 0).obj M) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex L (.up ℤ) 0).hom.app M) := by
    simp only [Functor.comp_obj, Functor.mapDerivedCategorySingleFunctor,
      DerivedCategory.singleFunctorIsoCompQ, Functor.isoWhiskerRight_refl,
      Functor.isoWhiskerLeft_refl, Iso.refl_symm, Iso.refl_trans, Iso.trans_hom,
      Functor.isoWhiskerLeft_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom, Iso.refl_hom,
      NatTrans.comp_app, Functor.associator_hom_app, Functor.whiskerLeft_app,
      Functor.associator_inv_app, DerivedCategory.Q_obj_single_obj,
      Functor.whiskerRight_app, NatTrans.id_app, Category.comp_id, Category.id_comp]
    erw [Category.id_comp]
    rfl
  rw [hs G, hs F]
  erw [← Category.assoc,
    exactMap_fac_Q α ((HomologicalComplex.single C (.up ℤ) 0).obj M)]
  change (F.mapDerivedCategoryFactors.hom.app
      ((HomologicalComplex.single C (.up ℤ) 0).obj M) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex α (.up ℤ)).app
        ((HomologicalComplex.single C (.up ℤ) 0).obj M))) ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).hom.app M) =
    (F.mapDerivedCategoryFactors.hom.app
      ((HomologicalComplex.single C (.up ℤ) 0).obj M) ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app M)) ≫
      DerivedCategory.Q.map ((HomologicalComplex.single D (.up ℤ) 0).map (α.app M))
  simp only [Category.assoc, ← DerivedCategory.Q.map_comp]
  congr 2
  ext n
  by_cases hn : n = 0
  · subst n
    simp [HomologicalComplex.single, HomologicalComplex.singleMapHomologicalComplex,
      NatTrans.mapHomologicalComplex]
  · simp [hn]

private noncomputable def sourceHomIso
    {C : Type*} [Category C] {M N : C} (e : M ≅ N) :
    coyoneda.obj (op M) ≅ coyoneda.obj (op N) :=
  NatIso.ofComponents (fun K ↦ (Iso.homCongr e (Iso.refl K)).toIso)
    (by intro K K' f; ext g; simp [Iso.homCongr, Category.assoc])

private noncomputable def derivedAdjointRepresentation
    (A : Type (u + 1)) [CommRing A]
    {C : Type*} [Category.{u + 1} C] [Abelian C] [HasDerivedCategory C]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    (L : ModuleCat.{u + 1} A ⥤ C) (R : C ⥤ ModuleCat.{u + 1} A)
    [L.Additive] [R.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (adj : L ⊣ R) (q : ℤ) :
    DerivedCategory.Plus.ι ⋙ R.rightDerivedFunctor ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) q ⋙
          forget (ModuleCat.{u + 1} A) ≅
      DerivedCategory.Plus.ι ⋙ shiftFunctor (DerivedCategory C) q ⋙
        coyoneda.obj (op ((DerivedCategory.singleFunctor C 0).obj
          (L.obj (ModuleCat.of A A)))) :=
  Functor.isoWhiskerLeft DerivedCategory.Plus.ι
      (adjointRepresentation A L.mapDerivedCategory R.rightDerivedFunctor
        adj.mapDerivedCategoryRightDerivedAdjunction q) ≪≫
    Functor.isoWhiskerLeft
      (DerivedCategory.Plus.ι ⋙ shiftFunctor (DerivedCategory C) q)
      (sourceHomIso ((L.mapDerivedCategorySingleFunctor 0).app (ModuleCat.of A A)))

private noncomputable def boundedDerivedAdjointRepresentation
    (A : Type (u + 1)) [CommRing A]
    {C : Type*} [Category.{u + 1} C] [Abelian C] [HasDerivedCategory C]
    [EnoughInjectives C] [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    (L : ModuleCat.{u + 1} A ⥤ C) (R : C ⥤ ModuleCat.{u + 1} A)
    [L.Additive] [R.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (adj : L ⊣ R) (q : ℤ) :
    R.rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) q ⋙
          forget (ModuleCat.{u + 1} A) ≅
      DerivedCategory.Plus.ι ⋙ shiftFunctor (DerivedCategory C) q ⋙
        coyoneda.obj (op ((DerivedCategory.singleFunctor C 0).obj
          (L.obj (ModuleCat.of A A)))) :=
  Functor.isoWhiskerRight R.rightDerivedFunctorPlusCompatibility
      (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) q ⋙
        forget (ModuleCat.{u + 1} A)) ≪≫
    derivedAdjointRepresentation A L R adj q

private theorem boundedRepresentation_naturality
    (A : Type (u + 1)) [CommRing A]
    {C : Type*} [Category.{u + 1} C] [Abelian C] [HasDerivedCategory C]
    [EnoughInjectives C] [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    {L L' : ModuleCat.{u + 1} A ⥤ C} {R R' : C ⥤ ModuleCat.{u + 1} A}
    [L.Additive] [R.Additive] [L'.Additive] [R'.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    (a : L ⊣ R) (a' : L' ⊣ R') (ρ : L' ⟶ L) (τ : R ⟶ R')
    (hρ : ∀ M K (f : L.obj M ⟶ K),
      a'.homEquiv M K (ρ.app M ≫ f) = a.homEquiv M K f ≫ τ.app K)
    (q : ℤ) (B : DerivedCategory.Plus C)
    (x : (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) q).obj
      (R.rightDerivedFunctorPlus.obj B)) :
    (boundedDerivedAdjointRepresentation A L' R' a' q).hom.app B
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) q).map
          ((Functor.rightDerivedFunctorPlusNatTrans τ).app B) x) =
      (DerivedCategory.singleFunctor C 0).map (ρ.app (ModuleCat.of A A)) ≫
        (boundedDerivedAdjointRepresentation A L R a q).hom.app B x := by
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) q
  let e := adjointRepresentation A L.mapDerivedCategory R.rightDerivedFunctor
    a.mapDerivedCategoryRightDerivedAdjunction q
  let e' := adjointRepresentation A L'.mapDerivedCategory R'.rightDerivedFunctor
    a'.mapDerivedCategoryRightDerivedAdjunction q
  let d := (L.mapDerivedCategorySingleFunctor 0).app (ModuleCat.of A A)
  let d' := (L'.mapDerivedCategorySingleFunctor 0).app (ModuleCat.of A A)
  let t := Functor.rightDerivedFunctorNatTrans τ
  let := rightDerivedNatTrans_commShift τ
  have ht (y : H.obj (R.rightDerivedFunctor.obj B.obj)) :
      e'.hom.app B.obj (H.map (t.app B.obj) y) =
        (Functor.exactDerivedMap ρ).app _ ≫ e.hom.app B.obj y := by
    apply (asIso (e'.inv.app B.obj)).toEquiv.injective
    have h := adjointRepresentation_naturality A
      a.mapDerivedCategoryRightDerivedAdjunction a'.mapDerivedCategoryRightDerivedAdjunction
      t (Functor.exactDerivedMap ρ) (derivedTranspose_naturality a a' ρ τ hρ)
      q B.obj (e.hom.app B.obj y)
    change e'.inv.app B.obj (e'.hom.app B.obj (H.map (t.app B.obj) y)) =
      e'.inv.app B.obj ((Functor.exactDerivedMap ρ).app _ ≫ e.hom.app B.obj y)
    change H.map (t.app B.obj) (e.inv.app B.obj (e.hom.app B.obj y)) =
      e'.inv.app B.obj ((Functor.exactDerivedMap ρ).app _ ≫ e.hom.app B.obj y) at h
    rw [natIso_hom_inv_apply] at h ⊢
    exact h
  have hc := congr_app (AlgebraicGeometry.ProEtale.compatibility_naturality τ) B
  have hc' := ConcreteCategory.congr_hom (congrArg H.map hc) x
  simp only [Functor.map_comp, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, ModuleCat.comp_apply] at hc'
  have hd := exactMap_single ρ (ModuleCat.of A A)
  change (Functor.exactDerivedMap ρ).app _ ≫ d.hom =
    d'.hom ≫ (DerivedCategory.singleFunctor C 0).map (ρ.app (ModuleCat.of A A)) at hd
  have hd' : d'.inv ≫ (Functor.exactDerivedMap ρ).app _ =
      (DerivedCategory.singleFunctor C 0).map (ρ.app (ModuleCat.of A A)) ≫ d.inv := by
    apply (cancel_mono d.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hd, Iso.inv_hom_id_assoc]
  change d'.inv ≫ e'.hom.app B.obj
      (H.map (R'.rightDerivedFunctorPlusCompatibility.hom.app B)
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} A) q).map
          ((Functor.rightDerivedFunctorPlusNatTrans τ).app B) x)) ≫ 𝟙 _ =
    (DerivedCategory.singleFunctor C 0).map (ρ.app (ModuleCat.of A A)) ≫
      (d.inv ≫ e.hom.app B.obj
        (H.map (R.rightDerivedFunctorPlusCompatibility.hom.app B) x) ≫ 𝟙 _)
  simp only [Category.comp_id]
  erw [hc', ht, ← Category.assoc, hd', Category.assoc]

private noncomputable def boundedHomEquiv
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (L : DerivedCategory C ⥤ DerivedCategory D)
    (hL : (DerivedCategory.Plus.ι ⋙ L).FullyFaithful)
    (M N : DerivedCategory.Plus C) :
    (M.obj ⟶ N.obj) ≃ (L.obj M.obj ⟶ L.obj N.obj) :=
  (Functor.FullyFaithful.ofFullyFaithful DerivedCategory.Plus.ι).homEquiv.symm.trans
    hL.homEquiv

private theorem boundedHomEquiv_apply
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (L : DerivedCategory C ⥤ DerivedCategory D)
    (hL : (DerivedCategory.Plus.ι ⋙ L).FullyFaithful)
    (M N : DerivedCategory.Plus C) (f : M.obj ⟶ N.obj) :
    boundedHomEquiv L hL M N f = L.map f := by
  change L.map (DerivedCategory.Plus.ι.map (DerivedCategory.Plus.ι.preimage f)) = L.map f
  rw [Functor.map_preimage]

private theorem singleBounded_property
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (M : C) : (DerivedCategory.TStructure.t (C := C)).plus
      ((DerivedCategory.singleFunctor C 0).obj M) := by
  exact ⟨0, inferInstance⟩

private theorem shiftedBounded_property
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (B : DerivedCategory.Plus C) (q : ℤ) :
    (DerivedCategory.TStructure.t (C := C)).plus (B.obj⟦q⟧) := by
  exact (DerivedCategory.TStructure.t (C := C)).plus.le_shift q B.obj B.property

private noncomputable def transportRepresentation
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (hL : L.mapDerivedCategoryPlus.FullyFaithful)
    (M : C) (N : D) (d : L.obj M ≅ N) (q : ℤ) :
    DerivedCategory.Plus.ι ⋙ shiftFunctor (DerivedCategory C) q ⋙
        coyoneda.obj (op ((DerivedCategory.singleFunctor C 0).obj M)) ≅
      L.mapDerivedCategoryPlus ⋙ DerivedCategory.Plus.ι ⋙
        shiftFunctor (DerivedCategory D) q ⋙
          coyoneda.obj (op ((DerivedCategory.singleFunctor D 0).obj N)) := by
  let h := (hL.comp
    (Functor.FullyFaithful.ofFullyFaithful DerivedCategory.Plus.ι)).ofIso
      L.mapDerivedCategoryPlusCompatibility
  let δ := (L.mapDerivedCategorySingleFunctor 0).app M ≪≫
    (DerivedCategory.singleFunctor D 0).mapIso d
  refine NatIso.ofComponents (fun B ↦
    ((boundedHomEquiv L.mapDerivedCategory h
        ⟨(DerivedCategory.singleFunctor C 0).obj M, singleBounded_property M⟩
        ⟨B.obj⟦q⟧, shiftedBounded_property B q⟩).trans
      (Iso.homCongr δ ((L.mapDerivedCategory.commShiftIso q).app B.obj))).toIso) ?_
  intro B B' f
  apply ConcreteCategory.hom_ext
  intro g
  change δ.inv ≫ boundedHomEquiv L.mapDerivedCategory h
      ⟨(DerivedCategory.singleFunctor C 0).obj M, singleBounded_property M⟩
      ⟨B'.obj⟦q⟧, shiftedBounded_property B' q⟩ (g ≫ f.hom⟦q⟧') ≫
        (L.mapDerivedCategory.commShiftIso q).hom.app B'.obj =
    (δ.inv ≫ boundedHomEquiv L.mapDerivedCategory h
      ⟨(DerivedCategory.singleFunctor C 0).obj M, singleBounded_property M⟩
      ⟨B.obj⟦q⟧, shiftedBounded_property B q⟩ g ≫
        (L.mapDerivedCategory.commShiftIso q).hom.app B.obj) ≫
          (L.mapDerivedCategory.map f.hom)⟦q⟧'
  rw [boundedHomEquiv_apply, boundedHomEquiv_apply]
  rw [L.mapDerivedCategory.map_comp]
  simp only [Category.assoc]
  rw [L.mapDerivedCategory.commShiftIso_hom_naturality]
  rfl

private theorem transportRepresentation_apply
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (hL : L.mapDerivedCategoryPlus.FullyFaithful)
    (M : C) (N : D) (d : L.obj M ≅ N) (q : ℤ)
    (B : DerivedCategory.Plus C)
    (f : (DerivedCategory.singleFunctor C 0).obj M ⟶ B.obj⟦q⟧) :
    (transportRepresentation L hL M N d q).hom.app B f =
      (DerivedCategory.singleFunctor D 0).map d.inv ≫
        (L.mapDerivedCategorySingleFunctor 0).inv.app M ≫ L.mapDerivedCategory.map f ≫
          (L.mapDerivedCategory.commShiftIso q).hom.app B.obj := by
  let h := (hL.comp
    (Functor.FullyFaithful.ofFullyFaithful DerivedCategory.Plus.ι)).ofIso
      L.mapDerivedCategoryPlusCompatibility
  change ((DerivedCategory.singleFunctor D 0).map d.inv ≫
      (L.mapDerivedCategorySingleFunctor 0).inv.app M) ≫
      boundedHomEquiv L.mapDerivedCategory h
        ⟨(DerivedCategory.singleFunctor C 0).obj M, singleBounded_property M⟩
        ⟨B.obj⟦q⟧, shiftedBounded_property B q⟩ f ≫
          (L.mapDerivedCategory.commShiftIso q).hom.app B.obj = _
  rw [boundedHomEquiv_apply]
  simp only [Category.assoc]

private theorem transportRepresentation_precompose
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (hL : L.mapDerivedCategoryPlus.FullyFaithful)
    {M M' : C} {N N' : D} (d : L.obj M ≅ N) (d' : L.obj M' ≅ N')
    (r : M ⟶ M') (t : N ⟶ N')
    (h : t ≫ d'.inv = d.inv ≫ L.map r)
    (q : ℤ) (B : DerivedCategory.Plus C)
    (f : (DerivedCategory.singleFunctor C 0).obj M' ⟶ B.obj⟦q⟧) :
    (transportRepresentation L hL M N d q).hom.app B
        ((DerivedCategory.singleFunctor C 0).map r ≫ f) =
      (DerivedCategory.singleFunctor D 0).map t ≫
        (transportRepresentation L hL M' N' d' q).hom.app B f := by
  rw [transportRepresentation_apply, transportRepresentation_apply]
  rw [L.mapDerivedCategory.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc ((DerivedCategory.singleFunctor D 0).map t),
    ← (DerivedCategory.singleFunctor D 0).map_comp, h,
    (DerivedCategory.singleFunctor D 0).map_comp, Category.assoc]
  have hn := (L.mapDerivedCategorySingleFunctor 0).inv.naturality r
  change (DerivedCategory.singleFunctor D 0).map (L.map r) ≫
      (L.mapDerivedCategorySingleFunctor 0).inv.app M' =
    (L.mapDerivedCategorySingleFunctor 0).inv.app M ≫
      L.mapDerivedCategory.map ((DerivedCategory.singleFunctor C 0).map r) at hn
  rw [← Category.assoc ((DerivedCategory.singleFunctor D 0).map (L.map r)), hn]
  simp only [Category.assoc]

/-- The ambient ordinary etale coefficient object.
Source: supported-Hom identification (blueprint: lem-pur-retracted-support-representability). -/
abbrev supportAmbientCoefficient : EtSheaves P X :=
  (constantSheaf X.smallEtaleTopology (Modules P)).obj (ModuleCat.of P.Coefficient P.Coefficient)

/-- The ordinary closed etale coefficient object.
Source: supported-Hom identification (blueprint: lem-pur-retracted-support-representability). -/
abbrev supportClosedCoefficient : EtSheaves P X :=
  (Etale.supportedCoefficients P.Coefficient s).obj (ModuleCat.of P.Coefficient P.Coefficient)

/-- The single-object realization before the epimorphism is used.
Source: supported-Hom identification (blueprint: lem-pur-retracted-support-representability). -/
abbrev supportSingle := DerivedCategory.singleFunctor (EtSheaves P X) 0

/-- Test objects are shifted ordinary bounded-below etale inputs, in the ambient category.
Source: fixed-degree Yoneda calculation
(blueprint: lem-pur-retracted-support-representability). -/
abbrev supportTests (q : ℤ) :=
  (DerivedCategory.Plus.ι : DerivedCategory.Plus (EtSheaves P X) ⥤ _) ⋙
    shiftFunctor (DerivedCategory (EtSheaves P X)) q

/-- The support groups, with the module structure forgotten only for Yoneda.
Source: supported-Hom identification (blueprint: lem-pur-retracted-support-representability). -/
abbrev supportValues (q : ℤ) :=
  nuPlus P X ⋙ Sheaf.supportHypercohomologyFunctor
    (Scheme.ProEt.topology X) (Modules P) (supportRestrictionArrow s) q ⋙ forget (Modules P)

/-- The ambient section groups in the same coordinates.
Source: supported-Hom identification (blueprint: lem-pur-retracted-support-representability). -/
abbrev supportAmbientValues (q : ℤ) :=
  nuPlus P X ⋙ Sheaf.sectionHypercohomologyFunctor
    (Scheme.ProEt.topology X) (Modules P) (Scheme.ProEt.mk (𝟙 X)) q ⋙ forget (Modules P)

/-- The actual supported-section inclusion, viewed as a transformation of sets.
Source: supported-Hom identification (blueprint: lem-pur-retracted-support-representability). -/
def supportForgetValues (q : ℤ) : supportValues P s q ⟶ supportAmbientValues P (X := X) q :=
  Functor.whiskerRight
    (Functor.whiskerLeft (nuPlus P X)
      (Sheaf.supportHypercohomologyInclusion (Scheme.ProEt.topology X) (Modules P)
        (supportRestrictionArrow s) q)) (forget (Modules P))

/-- Two ordinary Hom representations and the equation representing forgetting support.
This structure contains no comparison of exceptional functors and no Gysin morphism.
Source: closed-support Hom and the quotient normalization
(blueprint: lem-pur-retracted-support-representability). -/
structure SupportRepresentability (q : ℤ) where
  supported : supportValues P s q ≅
    supportTests P (X := X) q ⋙ coyoneda.obj (op ((supportSingle P).obj
      (supportClosedCoefficient P s)))
  ambient : supportAmbientValues P (X := X) q ≅
    supportTests P (X := X) q ⋙ coyoneda.obj (op ((supportSingle P).obj
      (supportAmbientCoefficient P (X := X))))
  quotient_epi : Epi (Etale.supportedCoefficientQuotient P.Coefficient s
    (ModuleCat.of P.Coefficient P.Coefficient))
  forget_eq : ∀ (B : DerivedCategory.Plus (EtSheaves P X))
    (x : (supportValues P s q).obj B),
    ambient.hom.app B ((supportForgetValues P s q).app B x) =
      (supportSingle P).map (Etale.supportedCoefficientQuotient P.Coefficient s
        (ModuleCat.of P.Coefficient P.Coefficient)) ≫ supported.hom.app B x

private noncomputable def ambientAdjunction :
    constantSheaf (Scheme.ProEt.topology X) (Modules P) ⊣
      (sheafSections (Scheme.ProEt.topology X) (Modules P)).obj
        (op (Scheme.ProEt.mk (𝟙 X))) :=
  (constantSheafΓAdj (Scheme.ProEt.topology X) (Modules P)).ofNatIsoRight
    (Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology X) (Modules P)
      (Scheme.ProEt.isTerminalMkId X))

private theorem ordinaryTranspose_quotient [IsLocallyNoetherian X]
    (M : Modules P) (F : ProSheaves P X)
    (f : (supportedCoefficients P.Coefficient s).obj M ⟶ F) :
    (ambientAdjunction P).homEquiv M F
        (supportedCoefficientQuotient P.Coefficient s M ≫ f) =
      (supportedCoefficientAdjunction P.Coefficient s).homEquiv M F f ≫
        (Sheaf.supportedSectionsInclusion (Scheme.ProEt.topology X) (Modules P)
          (supportRestrictionArrow s)).app F := by
  have h := (exists_unique_supportedCoefficientAdjunction P.Coefficient s).choose_spec.1
    M F ((supportedCoefficientAdjunction P.Coefficient s).homEquiv M F f)
  change supportedCoefficientQuotient P.Coefficient s M ≫
    ((supportedCoefficientAdjunction P.Coefficient s).homEquiv M F).symm
      ((supportedCoefficientAdjunction P.Coefficient s).homEquiv M F f) = _ at h
  rw [Equiv.symm_apply_apply] at h
  rw [h]
  simp only [ambientAdjunction, Adjunction.homEquiv_ofNatIsoRight_apply,
    Equiv.apply_symm_apply, supportedModuleSectionsι, NatTrans.comp_app, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id]
  rfl

private noncomputable def supportedProRepresentation [IsLocallyNoetherian X] (q : ℤ) :
    supportValues P s q ≅
      nuPlus P X ⋙ DerivedCategory.Plus.ι ⋙
        shiftFunctor (DerivedCategory (ProSheaves P X)) q ⋙
          coyoneda.obj (op ((DerivedCategory.singleFunctor (ProSheaves P X) 0).obj
            ((supportedCoefficients P.Coefficient s).obj
              (ModuleCat.of P.Coefficient P.Coefficient)))) :=
  Functor.isoWhiskerLeft (nuPlus P X)
    (boundedDerivedAdjointRepresentation P.Coefficient _ _
      (supportedCoefficientAdjunction P.Coefficient s) q)

private noncomputable def ambientProRepresentation (q : ℤ) :
    supportAmbientValues P (X := X) q ≅
      nuPlus P X ⋙ DerivedCategory.Plus.ι ⋙
        shiftFunctor (DerivedCategory (ProSheaves P X)) q ⋙
          coyoneda.obj (op ((DerivedCategory.singleFunctor (ProSheaves P X) 0).obj
            ((constantSheaf (Scheme.ProEt.topology X) (Modules P)).obj
              (ModuleCat.of P.Coefficient P.Coefficient)))) :=
  Functor.isoWhiskerLeft (nuPlus P X)
    (boundedDerivedAdjointRepresentation P.Coefficient _ _ (ambientAdjunction P) q)

private theorem proRepresentation_quotient [IsLocallyNoetherian X] (q : ℤ)
    (B : DerivedCategory.Plus (EtSheaves P X)) (x : (supportValues P s q).obj B) :
    (ambientProRepresentation P q).hom.app B ((supportForgetValues P s q).app B x) =
      (DerivedCategory.singleFunctor (ProSheaves P X) 0).map
          (supportedCoefficientQuotient P.Coefficient s
            (ModuleCat.of P.Coefficient P.Coefficient)) ≫
        (supportedProRepresentation P s q).hom.app B x := by
  exact boundedRepresentation_naturality P.Coefficient
    (supportedCoefficientAdjunction P.Coefficient s) (ambientAdjunction P)
    (coefficientQuotientNat P.Coefficient s)
    (Sheaf.supportedSectionsInclusion (Scheme.ProEt.topology X) (Modules P)
      (supportRestrictionArrow s))
    (ordinaryTranspose_quotient P s) q ((nuPlus P X).obj B) x

private theorem etaleToPro_quotient [IsLocallyNoetherian X] (q : ℤ)
    (B : DerivedCategory.Plus (EtSheaves P X))
    (f : (supportSingle P).obj (supportClosedCoefficient P s) ⟶
      (supportTests P q).obj B) :
    (ambientEtaleToPro P q).hom.app B
        ((supportSingle P).map (Etale.supportedCoefficientQuotient P.Coefficient s
          (ModuleCat.of P.Coefficient P.Coefficient)) ≫ f) =
      (DerivedCategory.singleFunctor (ProSheaves P X) 0).map
          (supportedCoefficientQuotient P.Coefficient s
            (ModuleCat.of P.Coefficient P.Coefficient)) ≫
        (supportedEtaleToPro P s q).hom.app B f := by
  exact transportRepresentation_precompose (comparisonUpperStar (Modules P) X) _
    ((constantComparison P.Coefficient X).app (ModuleCat.of P.Coefficient P.Coefficient))
    ((coefficientComparison P.Coefficient s).app (ModuleCat.of P.Coefficient P.Coefficient))
    _ _ (coefficientComparison_quotient P.Coefficient s
      (ModuleCat.of P.Coefficient P.Coefficient)) q B f

/-- Fixed-degree supported cohomology and ambient cohomology admit ordinary etale Hom
representations which turn forgetting support into precomposition by the coefficient
quotient. Source: `lem-pur-supported-hom.proof.md` and the second assertion of
`lem-pur-gysin-structure.proof.md`
(blueprint: lem-pur-retracted-support-representability).

Proof:
1. On a bounded-below injective complex, evaluation at one identifies supported sections
   with Hom from the ordinary closed constant coefficient object. The quotient
   normalization identifies the kernel inclusion with precomposition by the ambient
   constant quotient. Apply this degreewise and then pass to homology and localization.
2. The finite etale/pro-etale comparison is fully faithful on D+. The canonical closed
   direct-image mate identifies the pro-etale supported constant with the inverse image
   of the displayed etale coefficient. Its constant-unit equation fixes the scalar.
   The analogous constant comparison gives the ambient representation.
3. Derive the kernel-inclusion square. The derived-unit equations identify the two
   right-derived constructions on injectives, and naturality transports the square to
   every bounded-below input. Retain q as fixed throughout; no compatibility between
   arbitrarily chosen support isomorphisms in different degrees is asserted.
4. The ordinary quotient is the constant-sheaf image of the closed inverse-image unit.
   Its cokernel restricts to zero on both the closed part and its open complement;
   conservativity of the closed/open restrictions makes that cokernel zero. Hence the
   quotient is an epimorphism in sheaves, before applying the single functor.
   These constructions also apply to the zero coefficient module and empty schemes. -/
theorem supportRepresentability_exists [IsLocallyNoetherian X] (q : ℤ) :
    Nonempty (SupportRepresentability P s q) := by
  let es := supportedProRepresentation P s q
  let ea := ambientProRepresentation P (X := X) q
  let ts := supportedEtaleToPro P s q
  let ta := ambientEtaleToPro P (X := X) q
  refine ⟨⟨es ≪≫ ts.symm, ea ≪≫ ta.symm, ?_, ?_⟩⟩
  · exact Etale.coefficientQuotient_epi P.Coefficient s _
  · intro B x
    apply (asIso (ta.hom.app B)).toEquiv.injective
    change ta.hom.app B (ta.inv.app B (ea.hom.app B
        ((supportForgetValues P s q).app B x))) =
      ta.hom.app B ((supportSingle P).map
        (Etale.supportedCoefficientQuotient P.Coefficient s
          (ModuleCat.of P.Coefficient P.Coefficient)) ≫
            ts.inv.app B (es.hom.app B x))
    rw [natIso_inv_hom_apply ta, etaleToPro_quotient, natIso_inv_hom_apply ts]
    exact proRepresentation_quotient P s q B x

end AlgebraicGeometry.ProEtale.RetractedSupport
