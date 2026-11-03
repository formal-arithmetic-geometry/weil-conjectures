/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.OrdinaryScalarSite.ScalarSiteComparisonNormalizedData
import WeilConjectures.CategoryTheory.Adjunction.SquareCompatibleMate

/-! # Ordinary scalar/site delta and direct-image gamma mates

Source: det-prop-scalar-six-direct-image, Formal properties and Finite rings;
Stacks 03EL, 06YY, 07A7.
(blueprint: def-sfb-ordinary-scalar-site-comparisons).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor CategoryTheory.TwoSquare
namespace AlgebraicGeometry.ProEtale.OrdinaryScalarSite

/-- Delta is the published scalar/site inverse mate, equipped with its inverse.
Source: det-prop-scalar-six-direct-image, Finite rings; Stacks 07A4
(blueprint: def-sfb-ordinary-scalar-site-comparisons). -/
abbrev delta {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) (T : Scheme.{u}) :=
  CoefficientScalarRepresentatives.comparisonIso T a

private theorem coextension_unit
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (a : A →+* B)
    (M : Sheaf J (ModuleCat.{u + 1} B)) (U : Cᵒᵖ) :
    ((Sheaf.restrictCoextendScalarsAdj J a).unit.app M).hom.app U =
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1} a).unit.app (M.obj.obj U) := by
  change ((sheafToPresheaf J _).map
    ((Sheaf.restrictCoextendScalarsAdj J a).unit.app M)).app U = _
  rw [Sheaf.restrictCoextendScalarsAdj, Adjunction.map_restrictFullyFaithful_unit_app]
  simp

private theorem coextension_counit
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (a : A →+* B)
    (M : Sheaf J (ModuleCat.{u + 1} A)) (U : Cᵒᵖ) :
    ((Sheaf.restrictCoextendScalarsAdj J a).counit.app M).hom.app U =
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1} a).counit.app (M.obj.obj U) := by
  change ((sheafToPresheaf J _).map
    ((Sheaf.restrictCoextendScalarsAdj J a).counit.app M)).app U = _
  rw [Sheaf.restrictCoextendScalarsAdj, Adjunction.map_restrictFullyFaithful_counit_app]
  simp only [Functor.comp_obj, Functor.id_obj, Iso.refl_inv, NatTrans.id_app,
    NatTrans.comp_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]
  rfl

private theorem coextension_push_mate
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) (T : Scheme.{u}) :
    (mateEquiv (Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology T) a)
      (Sheaf.restrictCoextendScalarsAdj T.smallEtaleTopology a)).symm
      (TwoSquare.mk
        (sheafCompose (Scheme.ProEt.topology T) (ModuleCat.coextendScalars a))
        (comparisonLowerStar (ModuleCat.{u + 1} A) T)
        (comparisonLowerStar (ModuleCat.{u + 1} B) T)
        (sheafCompose T.smallEtaleTopology (ModuleCat.coextendScalars a)) (𝟙
        (comparisonLowerStar (ModuleCat.{u + 1} A) T ⋙
          sheafCompose T.smallEtaleTopology (ModuleCat.coextendScalars a)))) =
      TwoSquare.mk (comparisonLowerStar (ModuleCat.{u + 1} B) T)
        (Sheaf.restrictScalars (Scheme.ProEt.topology T) a)
        (Sheaf.restrictScalars T.smallEtaleTopology a)
        (comparisonLowerStar (ModuleCat.{u + 1} A) T) (𝟙
        (comparisonLowerStar (ModuleCat.{u + 1} B) T ⋙
          Sheaf.restrictScalars T.smallEtaleTopology a)) := by
  ext G U : 4
  simp only [Functor.comp_obj, mateEquiv_symm_apply, NatTrans.comp_app,
    Functor.id_obj, Functor.leftUnitor_inv_app, Functor.whiskerRight_app,
    Functor.comp_map, Functor.associator_inv_app, Functor.associator_hom_app,
    CategoryTheory.Functor.map_id, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    Category.comp_id, Category.id_comp, NatTrans.id_app]
  change (ModuleCat.restrictScalars a).map
      (((Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology T) a).unit.app G).hom.app
        ((Scheme.toProEt T).op.obj U)) ≫
    ((Sheaf.restrictCoextendScalarsAdj T.smallEtaleTopology a).counit.app
      ((Sheaf.restrictScalars T.smallEtaleTopology a).obj
        ((comparisonLowerStar (ModuleCat.{u + 1} B) T).obj G))).hom.app U = 𝟙 _
  rw [coextension_unit, coextension_counit]
  exact (ModuleCat.restrictCoextendScalarsAdj.{u + 1} a).left_triangle_components
    (G.obj.obj ((Scheme.toProEt T).op.obj U))

private theorem ordinary_scalar_mate
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) (T : Scheme.{u}) :
    mateEquiv (CoefficientScalarRepresentatives.ordinaryAdjunction T.smallEtaleTopology a)
      (CoefficientScalarRepresentatives.ordinaryAdjunction (Scheme.ProEt.topology T) a)
      (TwoSquare.mk _ _ _ _ (EtaleChartComparison.scalarSheafIso a T).inv) =
      TwoSquare.mk _ _ _ _ (CoefficientScalarRepresentatives.comparisonRestriction T a).inv := by
  apply (mateEquiv (comparisonAdjunction (ModuleCat.{u + 1} B) T)
    (comparisonAdjunction (ModuleCat.{u + 1} A) T)).injective
  have h := iterated_mateEquiv_conjugateEquiv
    (CoefficientScalarRepresentatives.ordinaryAdjunction T.smallEtaleTopology a)
    (CoefficientScalarRepresentatives.ordinaryAdjunction (Scheme.ProEt.topology T) a)
    (comparisonAdjunction (ModuleCat.{u + 1} A) T)
    (comparisonAdjunction (ModuleCat.{u + 1} B) T)
    (TwoSquare.mk _ _ _ _ (EtaleChartComparison.scalarSheafIso a T).inv)
  have hr := iterated_mateEquiv_conjugateEquiv_symm
    (comparisonAdjunction (ModuleCat.{u + 1} B) T)
    (comparisonAdjunction (ModuleCat.{u + 1} A) T)
    (Sheaf.restrictCoextendScalarsAdj T.smallEtaleTopology a)
    (Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology T) a)
    (TwoSquare.mk _ _ _ _ (𝟙
      (comparisonLowerStar (ModuleCat.{u + 1} A) T ⋙
        sheafCompose T.smallEtaleTopology (ModuleCat.coextendScalars a))))
  rw [coextension_push_mate a T] at hr
  have h0 : (conjugateEquiv
      ((CoefficientScalarRepresentatives.ordinaryAdjunction T.smallEtaleTopology a).comp
        (comparisonAdjunction (ModuleCat.{u + 1} B) T))
      ((comparisonAdjunction (ModuleCat.{u + 1} A) T).comp
        (CoefficientScalarRepresentatives.ordinaryAdjunction (Scheme.ProEt.topology T) a)))
      (EtaleChartComparison.scalarSheafIso a T).inv = 𝟙 _ := by
    change (conjugateEquiv _ _) ((conjugateEquiv _ _).symm (𝟙 _)) = _
    exact Equiv.apply_symm_apply _ _
  have hr' : (mateEquiv (comparisonAdjunction (ModuleCat.{u + 1} B) T)
      (comparisonAdjunction (ModuleCat.{u + 1} A) T)).symm
        (TwoSquare.mk (comparisonLowerStar (ModuleCat.{u + 1} B) T)
          (Sheaf.restrictScalars (Scheme.ProEt.topology T) a)
          (Sheaf.restrictScalars T.smallEtaleTopology a)
          (comparisonLowerStar (ModuleCat.{u + 1} A) T) (𝟙 _)) =
      TwoSquare.mk _ _ _ _ (CoefficientScalarRepresentatives.comparisonRestriction T a).inv :=
    hr
  rw [← hr', Equiv.apply_symm_apply]
  exact (TwoSquare.equivNatTrans _ _ _ _).injective (h.trans h0)

private def representativeSquare
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) :=
  (mateEquiv
    ((CoefficientScalarRepresentatives.ordinaryAdjunction J a).mapHomologicalComplex (.up ℤ))
    (CoefficientScalarRepresentatives.adjunction J a)).symm
    (TwoSquare.mk _ _ _ _ (Sheaf.restrictScalars J a).mapDerivedCategoryFactors.inv)

private theorem representativeSquare_app
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) (P : CochainComplex (Sheaf J (ModuleCat.{u + 1} A)) ℤ) :
    (representativeSquare J a).app P =
      CoefficientScalarRepresentatives.representative J a P := by
  have hunit :
      ((CoefficientScalarRepresentatives.ordinaryAdjunction J a).mapHomologicalComplex
        (.up ℤ)).unit.app P =
      (Functor.mapHomologicalComplexIdIso
        (Sheaf J (ModuleCat.{u + 1} A)) (.up ℤ)).inv.app P ≫
        (NatTrans.mapHomologicalComplex
          (CoefficientScalarRepresentatives.ordinaryAdjunction J a).unit (.up ℤ)).app P ≫
        (Functor.mapHomologicalComplexCompIso
          (F := CoefficientScalarRepresentatives.ordinaryExtension J a)
          (G := Sheaf.restrictScalars J a) (Iso.refl _) (.up ℤ)).inv.app P := by
    ext n : 1
    simp only [Adjunction.mapHomologicalComplex_unit_app_f, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplexIdIso_inv_app_f,
      Functor.mapHomologicalComplexCompIso_inv_app_f,
      NatTrans.mapHomologicalComplex_app_f, Iso.refl_inv, NatTrans.id_app]
    erw [Category.id_comp, Category.comp_id]
  simp only [representativeSquare, mateEquiv_symm_apply,
    CoefficientScalarRepresentatives.representative,
    Adjunction.homEquiv_counit, NatTrans.comp_app, Functor.comp_obj,
    Functor.id_obj, Functor.leftUnitor_inv_app, Functor.whiskerRight_app,
    Functor.comp_map, Functor.associator_inv_app, Functor.associator_hom_app,
    CategoryTheory.Functor.map_id, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    Category.comp_id, Category.id_comp, Functor.map_comp, Category.assoc, hunit]

private theorem square_factors
    {C D E V : Type*} [Category C] [Category D] [Category E] [Category V]
    [Abelian C] [Abelian D] [Abelian E] [Abelian V]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory V]
    (F₁ : C ⥤ D) (F₂ : D ⥤ V) (G₁ : C ⥤ E) (G₂ : E ⥤ V)
    [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂) (P : CochainComplex C ℤ) :
    (Functor.mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj P) ≫
        G₂.mapDerivedCategory.map (G₁.mapDerivedCategoryFactors.hom.app P) ≫
        G₂.mapDerivedCategoryFactors.hom.app
          ((G₁.mapHomologicalComplex (.up ℤ)).obj P) =
      F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.hom.app P) ≫
        F₂.mapDerivedCategoryFactors.hom.app
          ((F₁.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P) := by
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso F₁ F₂).hom.app
    (DerivedCategory.Q.obj P))).1
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors,
    Functor.mapDerivedCategoryNatIso_fac,
    Functor.mapDerivedCategoryCompIso_hom_app_factors_assoc]
  rfl

private theorem mate_pasting
    {C D E F C' D' E' F' : Type*}
    [Category C] [Category D] [Category E] [Category F]
    [Category C'] [Category D'] [Category E'] [Category F']
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    {L₁' : C' ⥤ D'} {R₁' : D' ⥤ C'} {L₂' : E' ⥤ F'} {R₂' : F' ⥤ E'}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (adj₁' : L₁' ⊣ R₁') (adj₂' : L₂' ⊣ R₂')
    {Q₁ : C ⥤ C'} {Q₂ : D ⥤ D'} {Q₃ : E ⥤ E'} {Q₄ : F ⥤ F'}
    {G : C ⥤ E} {H : D ⥤ F} {G' : C' ⥤ E'} {H' : D' ⥤ F'}
    (a : TwoSquare G L₁ L₂ H) (a' : TwoSquare G' L₁' L₂' H')
    (q₁ : TwoSquare Q₁ L₁ L₁' Q₂) (q₂ : TwoSquare Q₃ L₂ L₂' Q₄)
    (rG : Q₁ ⋙ G' ⟶ G ⋙ Q₃) (rH : Q₂ ⋙ H' ⟶ H ⋙ Q₄)
    (h : Functor.whiskerLeft R₁ rG ≫
        ((mateEquiv adj₁ adj₂ a) ≫ᵥ (mateEquiv adj₂ adj₂' q₂)).natTrans =
      ((mateEquiv adj₁ adj₁' q₁) ≫ᵥ (mateEquiv adj₁' adj₂' a')).natTrans ≫
        Functor.whiskerRight rH R₂') :
    Functor.whiskerRight rG L₂' ≫ (a ≫ₕ q₂).natTrans =
      (q₁ ≫ₕ a').natTrans ≫ Functor.whiskerLeft L₁ rH := by
  apply (mateEquiv adj₁ adj₂').injective
  rw [mateEquiv_whiskerRight_comp, mateEquiv_comp_whiskerLeft,
    mateEquiv_vcomp, mateEquiv_vcomp]
  exact h

private theorem delta_equation {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) (T : Scheme.{u})
    (P : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    (delta a T).inv.app (DerivedCategory.Q.obj P) ≫
        (scalar (Scheme.ProEt.topology T) a).map
          ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryFactors.hom.app P) ≫
        CoefficientScalarRepresentatives.representative (Scheme.ProEt.topology T) a
          (((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapHomologicalComplex
            (.up ℤ)).obj P) =
      (comparisonUpperStar (ModuleCat.{u + 1} B) T).mapDerivedCategory.map
          (CoefficientScalarRepresentatives.representative T.smallEtaleTopology a P) ≫
        (comparisonUpperStar (ModuleCat.{u + 1} B) T).mapDerivedCategoryFactors.hom.app
          (((CoefficientScalarRepresentatives.ordinaryExtension
            T.smallEtaleTopology a).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (EtaleChartComparison.scalarSheafIso a T)
            (.up ℤ)).hom.app P) := by
  let FA := comparisonUpperStar (ModuleCat.{u + 1} A) T
  let FB := comparisonUpperStar (ModuleCat.{u + 1} B) T
  let R₁ := Sheaf.restrictScalars T.smallEtaleTopology a
  let R₂ := Sheaf.restrictScalars (Scheme.ProEt.topology T) a
  let E₁ := CoefficientScalarRepresentatives.ordinaryExtension T.smallEtaleTopology a
  let E₂ := CoefficientScalarRepresentatives.ordinaryExtension (Scheme.ProEt.topology T) a
  let adj₁ := CoefficientScalarRepresentatives.ordinaryAdjunction T.smallEtaleTopology a
  let adj₂ := CoefficientScalarRepresentatives.ordinaryAdjunction (Scheme.ProEt.topology T) a
  let adj₁' := CoefficientScalarRepresentatives.adjunction T.smallEtaleTopology a
  let adj₂' := CoefficientScalarRepresentatives.adjunction (Scheme.ProEt.topology T) a
  let e := EtaleChartComparison.scalarSheafIso a T
  let r := CoefficientScalarRepresentatives.comparisonRestriction T a
  let α : TwoSquare (FA.mapHomologicalComplex (.up ℤ))
      (E₁.mapHomologicalComplex (.up ℤ)) (E₂.mapHomologicalComplex (.up ℤ))
      (FB.mapHomologicalComplex (.up ℤ)) :=
    TwoSquare.mk _ _ _ _ (NatIso.mapHomologicalComplex e (.up ℤ)).inv
  let α' := (mateEquiv adj₁' adj₂').symm
    (TwoSquare.mk _ _ _ _ (CoefficientScalarRepresentatives.derivedComparisonRestriction T a).inv)
  have hα : mateEquiv (adj₁.mapHomologicalComplex (.up ℤ))
      (adj₂.mapHomologicalComplex (.up ℤ)) α =
      TwoSquare.mk (R₁.mapHomologicalComplex (.up ℤ))
        (FB.mapHomologicalComplex (.up ℤ)) (FA.mapHomologicalComplex (.up ℤ))
        (R₂.mapHomologicalComplex (.up ℤ))
        (NatIso.mapHomologicalComplex r (.up ℤ)).inv := by
    ext M n : 2
    have h := congr_app (congrArg TwoSquare.natTrans (ordinary_scalar_mate a T)) (M.X n)
    simp only [mateEquiv_apply, NatTrans.comp_app, Functor.comp_obj, Functor.comp_map,
      Functor.id_obj, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app,
      Category.comp_id, Category.id_comp] at h
    dsimp only [TwoSquare.mk, TwoSquare.natTrans] at h
    dsimp only [α, FA, FB, R₁, R₂, adj₁, adj₂, e, r]
    simp only [mateEquiv_apply, NatTrans.comp_app, Functor.comp_obj, Functor.comp_map,
      Functor.id_obj, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app,
      Category.comp_id, Category.id_comp, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplex_map_f,
      Adjunction.mapHomologicalComplex_unit_app_f,
      Adjunction.mapHomologicalComplex_counit_app_f, NatIso.mapHomologicalComplex_inv_app_f]
    exact h
  have hright : Functor.whiskerLeft (R₁.mapHomologicalComplex (.up ℤ))
        FA.mapDerivedCategoryFactors.hom ≫
      ((mateEquiv (adj₁.mapHomologicalComplex (.up ℤ))
          (adj₂.mapHomologicalComplex (.up ℤ)) α) ≫ᵥ
        (mateEquiv (adj₂.mapHomologicalComplex (.up ℤ)) adj₂'
          (representativeSquare (Scheme.ProEt.topology T) a))).natTrans =
      ((mateEquiv (adj₁.mapHomologicalComplex (.up ℤ)) adj₁'
          (representativeSquare T.smallEtaleTopology a)) ≫ᵥ
        (mateEquiv adj₁' adj₂' α')).natTrans ≫
      Functor.whiskerRight FB.mapDerivedCategoryFactors.hom R₂.mapDerivedCategory := by
    rw [hα]
    dsimp only [representativeSquare, α', adj₁, adj₂, adj₁', adj₂']
    simp only [Equiv.apply_symm_apply]
    apply NatTrans.ext
    funext M
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      TwoSquare.vComp_app, Category.assoc]
    change FA.mapDerivedCategoryFactors.hom.app
        ((R₁.mapHomologicalComplex (.up ℤ)).obj M) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex r (.up ℤ)).inv.app M) ≫
        R₂.mapDerivedCategoryFactors.inv.app
          ((FB.mapHomologicalComplex (.up ℤ)).obj M) =
      FA.mapDerivedCategory.map (R₁.mapDerivedCategoryFactors.inv.app M) ≫
        (Functor.mapDerivedCategorySquareIso r).inv.app (DerivedCategory.Q.obj M) ≫
        R₂.mapDerivedCategory.map (FB.mapDerivedCategoryFactors.hom.app M)
    have hs := square_factors R₁ FA FB R₂ r.symm M
    apply (cancel_epi (FA.mapDerivedCategory.map
      (R₁.mapDerivedCategoryFactors.hom.app M))).1
    apply (cancel_mono (R₂.mapDerivedCategoryFactors.hom.app
      ((FB.mapHomologicalComplex (.up ℤ)).obj M))).1
    simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
      Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
    erw [Category.comp_id]
    simpa only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app, NatIso.mapHomologicalComplex,
      Functor.mapDerivedCategoryNatIso_symm, Category.assoc] using hs.symm
  have hp := congr_app (mate_pasting
    (adj₁.mapHomologicalComplex (.up ℤ)) (adj₂.mapHomologicalComplex (.up ℤ))
    adj₁' adj₂' α α' (representativeSquare T.smallEtaleTopology a)
    (representativeSquare (Scheme.ProEt.topology T) a)
    FA.mapDerivedCategoryFactors.hom FB.mapDerivedCategoryFactors.hom hright) P
  have hp' :
      (scalar (Scheme.ProEt.topology T) a).map (FA.mapDerivedCategoryFactors.hom.app P) ≫
        CoefficientScalarRepresentatives.representative (Scheme.ProEt.topology T) a
          ((FA.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).inv.app P) =
      (delta a T).hom.app (DerivedCategory.Q.obj P) ≫
        FB.mapDerivedCategory.map
          (CoefficientScalarRepresentatives.representative T.smallEtaleTopology a P) ≫
        FB.mapDerivedCategoryFactors.hom.app
          ((E₁.mapHomologicalComplex (.up ℤ)).obj P) := by
    simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      TwoSquare.hComp_app, representativeSquare_app, α, α',
      delta, CoefficientScalarRepresentatives.comparisonIso,
      CoefficientScalarRepresentatives.comparisonMap, asIso_hom, Category.assoc] using hp
  apply (cancel_epi ((delta a T).hom.app (DerivedCategory.Q.obj P))).1
  simp only [Iso.hom_inv_id_app_assoc]
  have hpp := congrArg (fun k ↦ k ≫
    DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P)) hp'
  simp only [Category.assoc, ← DerivedCategory.Q.map_comp, Iso.inv_hom_id_app] at hpp
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at hpp
  exact hpp

/-- The scalar direct-image mate on the etale site. Its transpose is scalar
extension of the counit after the normalized pullback/tensor comparison.
Source: det-prop-scalar-six-direct-image, Formal properties; Stacks 07A7
(blueprint: def-sfb-ordinary-scalar-site-comparisons). -/
def etaleGamma {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (mateEquiv
    (Etale.mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (Etale.mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
    (etaleIso a f).hom).natTrans

/-- The scalar direct-image mate on the pro-etale site. This construction does
not invert the mate. Source: det-prop-scalar-six-direct-image; Stacks 07A7
(blueprint: def-sfb-ordinary-scalar-site-comparisons). -/
def proEtaleGamma {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (mateEquiv
    ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).ofNatIsoLeft
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f))
    ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f).ofNatIsoLeft
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) f))
    (proEtaleIso a f).hom).natTrans

end AlgebraicGeometry.ProEtale.OrdinaryScalarSite
