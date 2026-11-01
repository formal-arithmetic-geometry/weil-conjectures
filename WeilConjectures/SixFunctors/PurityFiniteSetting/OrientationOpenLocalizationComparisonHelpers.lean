/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.PurityAffineLineOrientationData
public import WeilConjectures.CategoryTheory.Derived.DerivedExactSquareSupplement
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.CategoryTheory.Derived.DerivedComplexUnitCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChangeComp
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CommIsoComp

/-! Internal coherence lemmas for open localization comparison. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.RetractedSupport

namespace WeilConjectures.PurityFiniteSetting

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option maxHeartbeats 800000 in
-- Expanding the composite adjunction mates exceeds the default elaboration limit.
lemma restriction_iso_conjugate
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    conjugateEquiv
      ((comparisonAdjunction (ModuleCat.{u + 1} A) X).comp
        (openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) j))
      ((Etale.openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) j).comp
        (comparisonAdjunction (ModuleCat.{u + 1} A) U))
      (supportBoundaryOpenCoefficientIso A j).hom =
        (supportSiteComparisonCoefficientDirectImageIso (ModuleCat.{u + 1} A) j).hom := by
  let B := ModuleCat.{u + 1} A
  let r₀ := Etale.upperStarLowerStarAdjunction B j
  let r := Etale.openImmersionRestrictionLowerStarAdjunction B j
  let s₀ := upperStarLowerStarAdjunction B j
  let s := openImmersionRestrictionLowerStarAdjunction B j
  let cU := comparisonAdjunction B U
  let cX := comparisonAdjunction B X
  change conjugateEquiv (cX.comp s) (r.comp cU)
    (Functor.whiskerRight (Etale.upperStarIsoOpenImmersionRestriction B j).inv _ ≫
      (supportSiteComparisonCoefficientPullbackIso B j).hom ≫
        Functor.whiskerLeft (comparisonUpperStar B X)
          (upperStarIsoOpenImmersionRestriction B j).hom) = _
  erw [← conjugateEquiv_comp (cX.comp s) (r₀.comp cU) (r.comp cU),
    ← conjugateEquiv_comp (cX.comp s) (cX.comp s₀) (r₀.comp cU),
    conjugateEquiv_whiskerLeft s s₀ cX
      (upperStarIsoOpenImmersionRestriction B j).hom,
    conjugateEquiv_whiskerRight r₀ r cU
      (Etale.upperStarIsoOpenImmersionRestriction B j).inv]
  have he : conjugateEquiv r₀ r
      (Etale.upperStarIsoOpenImmersionRestriction B j).inv = 𝟙 _ :=
    conjugateEquiv_leftAdjointUniq_inv _ _
  have hp : conjugateEquiv s s₀
      (upperStarIsoOpenImmersionRestriction B j).hom = 𝟙 _ :=
    conjugateEquiv_leftAdjointUniq_hom _ _
  erw [he, hp]
  change (𝟙 _ ≫ (conjugateEquiv (cX.comp s₀) (r₀.comp cU))
    (supportSiteComparisonCoefficientPullbackIso B j).hom) ≫ 𝟙 _ = _
  erw [Category.id_comp, Category.comp_id]
  exact congrArg Iso.inv
    ((conjugateIsoEquiv (r₀.comp cU) (cX.comp s₀)).apply_symm_apply
      (supportSiteComparisonCoefficientDirectImageIso B j).symm)

set_option backward.defeqAttrib.useBackward true in
lemma restriction_direct_image_mate
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (mateEquiv
      (openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) j)
      (Etale.openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) j)
      (TwoSquare.mk
        (comparisonLowerStar (ModuleCat.{u + 1} A) X)
        (openImmersionRestriction (ModuleCat.{u + 1} A) j)
        (Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j)
        (comparisonLowerStar (ModuleCat.{u + 1} A) U) (𝟙 _))
      ).natTrans =
        (supportSiteComparisonCoefficientDirectImageIso (ModuleCat.{u + 1} A) j).hom := by
  ext M : 2
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun W ↦ ?_)
  simp only [Functor.comp_obj, mateEquiv_apply, NatTrans.comp_app, Functor.id_obj,
    Functor.rightUnitor_inv_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerRight_app, Functor.comp_map,
    Functor.leftUnitor_hom_app, Category.comp_id, Category.id_comp,
    ObjectProperty.FullSubcategory.comp_hom]
  change M.obj.map _ ≫ (𝟙 _ ≫ (𝟙 _ ≫ M.obj.map _)) =
    𝟙 _ ≫ M.obj.map _ ≫ 𝟙 _
  simp only [Category.id_comp, Category.comp_id, ← Functor.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  apply MorphismProperty.Over.Hom.ext
  apply Limits.pullback.hom_ext <;>
    simp [MorphismProperty.Over.pullback, Scheme.toProEt,
      supportSiteComparisonSiteBaseChangeIso]
  rfl

theorem open_unit_normalized (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    SupportBoundaryOpenUnitNormalized A j := by
  let B := ModuleCat.{u + 1} A
  let cU := comparisonAdjunction B U
  let cX := comparisonAdjunction B X
  let r := Etale.openImmersionRestrictionLowerStarAdjunction B j
  let s := openImmersionRestrictionLowerStarAdjunction B j
  let α := TwoSquare.mk _ _ _ _ (supportBoundaryOpenCoefficientIso A j).hom
  let θ := TwoSquare.mk (comparisonLowerStar B X) (openImmersionRestriction B j)
    (Etale.openImmersionRestriction B j) (comparisonLowerStar B U) (𝟙 _)
  have ha : mateEquiv cX cU α = θ := by
    apply (mateEquiv s r).injective
    apply (TwoSquare.equivNatTrans _ _ _ _).injective
    change (mateEquiv s r (mateEquiv cX cU α)).natTrans =
      (mateEquiv s r θ).natTrans
    erw [iterated_mateEquiv_conjugateEquiv]
    exact (restriction_iso_conjugate A j).trans
      (restriction_direct_image_mate A j).symm
  intro F
  have hu := unit_mateEquiv cX cU α F
  erw [ha] at hu
  change (Etale.openImmersionRestriction B j).map (cX.unit.app F) =
    cU.unit.app ((Etale.openImmersionRestriction B j).obj F) ≫
      (comparisonLowerStar B U).map ((supportBoundaryOpenCoefficientIso A j).hom.app F)
  change (Etale.openImmersionRestriction B j).map (cX.unit.app F) ≫ 𝟙 _ = _ at hu
  simpa only [α, Functor.id_obj, Category.comp_id] using hu

theorem comparison_pullback_eq (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) :
    supportSiteComparisonCoefficientPullbackIso (ModuleCat.{u + 1} A) j =
      (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) j).symm := by
  have hs : supportSiteComparisonSiteBaseChangeIso j = toProEtCompOverPullbackIso j := by
    ext W
    rfl
  unfold supportSiteComparisonCoefficientPullbackIso comparisonUpperStarCompUpperStarIso
  unfold supportSiteComparisonCoefficientDirectImageIso lowerStarCompComparisonLowerStarIso
  erw [hs]
  rfl

set_option maxRecDepth 2048 in
set_option maxHeartbeats 800000 in
-- Derived-category mate normalization needs the expanded heartbeat budget.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- Expanding the two restriction isomorphisms involves deeply nested sheaf functors.
theorem underived_open_square (P : PurityFiniteSetting.{u})
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (F : Sheaf X.smallEtaleTopology (Modules P)) :
    (P.coordinateOpenSectionsIso j).inv.app F ≫
        (finiteComparisonSectionUnit U P.Coefficient (Scheme.Etale.mk (𝟙 U))).app
          ((Etale.upperStar (Modules P) j).obj F) ≫
        (globalSectionsFunctor (Modules P) U).map
          ((comparisonUpperStarCompUpperStarIso (Modules P) j).inv.app F) =
      (finiteComparisonSectionUnit X P.Coefficient (Scheme.Etale.mk j)).app F ≫
        (openSectionsIso P j).inv.app ((comparisonUpperStar (Modules P) X).obj F) := by
  let B := Modules P
  let N := comparisonUpperStar B X
  let N' := comparisonUpperStar B U
  let r := Etale.openImmersionRestriction B j
  let I : Etale.upperStar B j ≅ r := Etale.upperStarIsoOpenImmersionRestriction B j
  let J : upperStar B j ≅ openImmersionRestriction B j :=
    upperStarIsoOpenImmersionRestriction B j
  let e := comparisonUpperStarCompUpperStarIso B j
  let T := Scheme.Etale.mk (𝟙 U)
  let eE : Scheme.Etale.mk j ≅
      (MorphismProperty.Over.map ⊤ (inferInstance : Etale j)).obj T :=
    MorphismProperty.Over.isoMk (Iso.refl _) (Category.id_comp _)
  let eP : Scheme.ProEt.mk j ≅
      (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).obj
        (Scheme.ProEt.mk (𝟙 U)) :=
    MorphismProperty.Over.isoMk (Iso.refl _) (Category.id_comp _)
  have hn := congrArg
    (fun z : r.obj F ⟶ r.obj ((comparisonLowerStar B X).obj (N.obj F)) ↦
      z.hom.app (op T)) (open_unit_normalized.{u} P.Coefficient j F)
  simp only [supportBoundaryOpenCoefficientIso, comparison_pullback_eq,
    Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatTrans.comp_app, Functor.map_comp, ObjectProperty.FullSubcategory.comp_hom] at hn
  have hw := congrArg
    (fun z : r.obj F ⟶ (comparisonLowerStar B U).obj
        (N'.obj ((Etale.upperStar B j).obj F)) ↦ z.hom.app (op T))
    ((comparisonAdjunction B U).unit.naturality (I.inv.app F))
  simp only [Functor.id_map, ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.comp_app] at hw
  apply (Iso.cancel_iso_hom_right _ _ ((openSectionsIso.{u} P j).app (N.obj F))).mp
  simp only [Iso.app_hom, Category.assoc]
  erw [Iso.inv_hom_id_app, Category.comp_id]
  change F.obj.map eE.hom.op ≫ (I.inv.app F).hom.app (op T) ≫
      ((comparisonAdjunction B U).unit.app ((Etale.upperStar B j).obj F)).hom.app (op T) ≫
      (e.inv.app F).hom.app (op (Scheme.ProEt.mk (𝟙 U))) ≫
      (J.hom.app (N.obj F)).hom.app (op (Scheme.ProEt.mk (𝟙 U))) ≫
      (N.obj F).obj.map eP.inv.op =
    ((comparisonAdjunction B X).unit.app F).hom.app (op (Scheme.Etale.mk j))
  erw [reassoc_of% hw]
  change F.obj.map eE.hom.op ≫
      (((comparisonAdjunction B U).unit.app (r.obj F)).hom.app (op T) ≫
        (N'.map (I.inv.app F)).hom.app (op (Scheme.ProEt.mk (𝟙 U))) ≫
        (e.inv.app F).hom.app (op (Scheme.ProEt.mk (𝟙 U))) ≫
        (J.hom.app (N.obj F)).hom.app (op (Scheme.ProEt.mk (𝟙 U)))) ≫
      (N.obj F).obj.map eP.inv.op = _
  erw [← hn]
  erw [((comparisonAdjunction B X).unit.app F).hom.naturality_assoc]
  erw [← (N.obj F).obj.map_comp]
  have he : ((Scheme.toProEt X).map eE.hom).op ≫ eP.inv.op = 𝟙 _ := by
    apply Quiver.Hom.unop_inj
    apply MorphismProperty.Over.Hom.ext
    change (𝟙 U) ≫ 𝟙 U = 𝟙 U
    simp
  change _ ≫ (N.obj F).obj.map (((Scheme.toProEt X).map eE.hom).op ≫ eP.inv.op) = _
  erw [he, CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

theorem inclusion_exact_map
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {K L : DerivedCategory.Plus C} (f : K ⟶ L) :
    DerivedCategory.Plus.ι.map (F.mapDerivedCategoryPlus.map f) =
      F.mapDerivedCategory.map (DerivedCategory.Plus.ι.map f) := rfl

theorem inclusion_single_map
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {X Y : C} (f : X ⟶ Y) :
    DerivedCategory.Plus.ι.map ((DerivedCategory.Plus.singleFunctor C 0).map f) =
      (DerivedCategory.singleFunctor C 0).map f := rfl

theorem plus_comp_single
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (X : C) :
    (Functor.mapDerivedCategoryPlusCompIso F G).hom.app
        ((DerivedCategory.Plus.singleFunctor C 0).obj X) ≫
      G.mapDerivedCategoryPlus.map ((F.mapDerivedCategoryPlusSingleFunctor 0).hom.app X) ≫
      (G.mapDerivedCategoryPlusSingleFunctor 0).hom.app (F.obj X) =
    ((F ⋙ G).mapDerivedCategoryPlusSingleFunctor 0).hom.app X := by
  apply DerivedCategory.Plus.ι.map_injective
  simpa only [Functor.map_comp, inclusion_exact_map,
    DerivedCategory.Plus.singleFunctor, DerivedCategory.Plus.singleFunctors,
    SingleFunctors.lift, Functor.comp_obj, Functor.comp_map,
    ObjectProperty.lift_obj_obj, ObjectProperty.ι_obj,
    Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app,
    Functor.ι_map_mapDerivedCategoryPlusSingleFunctor_hom_app] using
      Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor F G X

theorem plus_nat_single
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) (X : C) :
    (Functor.mapDerivedCategoryPlusNatIso e).hom.app
        ((DerivedCategory.Plus.singleFunctor C 0).obj X) ≫
      (G.mapDerivedCategoryPlusSingleFunctor 0).hom.app X =
    (F.mapDerivedCategoryPlusSingleFunctor 0).hom.app X ≫
      (DerivedCategory.Plus.singleFunctor D 0).map (e.hom.app X) := by
  apply DerivedCategory.Plus.ι.map_injective
  simp only [Functor.map_comp, inclusion_single_map,
    Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
    Functor.ι_map_mapDerivedCategoryPlusSingleFunctor_hom_app]
  change (Functor.mapDerivedCategoryNatIso e).hom.app
        ((DerivedCategory.singleFunctor C 0).obj X) ≫
      (G.mapDerivedCategorySingleFunctor 0).hom.app X =
    (F.mapDerivedCategorySingleFunctor 0).hom.app X ≫
      (DerivedCategory.singleFunctor D 0).map (e.hom.app X)
  exact Functor.mapDerivedCategoryNatIso_hom_app_singleFunctor e X

theorem plus_square_single
    {C D E T : Type*} [Category C] [Category D] [Category E] [Category T]
    [Abelian C] [Abelian D] [Abelian E] [Abelian T]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory T]
    (R : C ⥤ D) (G : D ⥤ T) (L : C ⥤ E) (S : E ⥤ T)
    [R.Additive] [G.Additive] [L.Additive] [S.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (e : R ⋙ G ≅ L ⋙ S) (X : C) :
    (Functor.mapDerivedCategoryPlusSquareIso R G L S e).hom.app
        ((DerivedCategory.Plus.singleFunctor C 0).obj X) ≫
      S.mapDerivedCategoryPlus.map ((L.mapDerivedCategoryPlusSingleFunctor 0).hom.app X) ≫
      (S.mapDerivedCategoryPlusSingleFunctor 0).hom.app (L.obj X) =
    G.mapDerivedCategoryPlus.map ((R.mapDerivedCategoryPlusSingleFunctor 0).hom.app X) ≫
      (G.mapDerivedCategoryPlusSingleFunctor 0).hom.app (R.obj X) ≫
      (DerivedCategory.Plus.singleFunctor T 0).map (e.hom.app X) := by
  let : PreservesFiniteLimits (R ⋙ G) := comp_preservesFiniteLimits _ _
  let : PreservesFiniteColimits (R ⋙ G) := comp_preservesFiniteColimits _ _
  let : PreservesFiniteLimits (L ⋙ S) := comp_preservesFiniteLimits _ _
  let : PreservesFiniteColimits (L ⋙ S) := comp_preservesFiniteColimits _ _
  simp only [Functor.mapDerivedCategoryPlusSquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc]
  erw [plus_comp_single L S, plus_nat_single, ← plus_comp_single R G]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]

theorem exact_factor_compat
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [EnoughInjectives C] [HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    Functor.whiskerRight F.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom
        DerivedCategory.Plus.ι =
      F.rightDerivedFunctorPlusCompatibility.hom ≫
        Functor.whiskerLeft DerivedCategory.Plus.ι
          F.rightDerivedFunctorIsoMapDerivedCategory.hom := by
  apply Functor.rightDerived_ext (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι)
    F.rightDerivedFunctorPlusιUnit (HomotopyCategory.Plus.quasiIso C)
  apply NatTrans.ext
  funext K
  simp only [Functor.rightDerivedFunctorPlusιUnit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  have hp := congr_app F.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus_hom_fac K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hp
  erw [← Functor.map_comp, hp]
  erw [reassoc_of% (CategoryTheory.derivedComplexUnitCompatibility.2.2.2 F K)]
  have hu := congr_app F.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
    ((HomotopyCategory.Plus.ι C).obj K)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hu
  erw [hu]
  have he : DerivedCategory.Plus.ι.mapIso (F.mapDerivedCategoryPlusFactorsh.app K) =
      F.mapDerivedCategoryFactorsh.app ((HomotopyCategory.Plus.ι C).obj K) := by
    apply Iso.ext
    exact F.ι_map_mapDerivedCategoryPlusFactorsh_hom_app K
  exact congrArg Iso.inv he

theorem derived_comp_compat
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [EnoughInjectives C] [EnoughInjectives D]
    [HasKInjectiveResolutions C] [HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [F.PreservesInjectiveObjects] [F.PreservesKInjectiveComplexes]
    (K : DerivedCategory.Plus C) :
    DerivedCategory.Plus.ι.map ((Functor.rightDerivedFunctorPlusCompIso F G).hom.app K) ≫
        G.rightDerivedFunctorPlusCompatibility.hom.app (F.rightDerivedFunctorPlus.obj K) ≫
        G.rightDerivedFunctor.map (F.rightDerivedFunctorPlusCompatibility.hom.app K) =
      (F ⋙ G).rightDerivedFunctorPlusCompatibility.hom.app K ≫
        (Functor.rightDerivedFunctorCompIso F G).hom.app K.obj := by
  let τ₁ := Functor.whiskerRight (Functor.rightDerivedFunctorPlusCompIso F G).hom
      DerivedCategory.Plus.ι ≫
    Functor.whiskerLeft F.rightDerivedFunctorPlus G.rightDerivedFunctorPlusCompatibility.hom ≫
    Functor.whiskerRight F.rightDerivedFunctorPlusCompatibility.hom G.rightDerivedFunctor
  let τ₂ := (F ⋙ G).rightDerivedFunctorPlusCompatibility.hom ≫
    Functor.whiskerLeft DerivedCategory.Plus.ι (Functor.rightDerivedFunctorCompIso F G).hom
  have ht : τ₁ = τ₂ := by
    apply Functor.rightDerived_ext ((F ⋙ G).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι)
      (F ⋙ G).rightDerivedFunctorPlusιUnit (HomotopyCategory.Plus.quasiIso C)
    apply NatTrans.ext
    funext L
    simp only [τ₁, τ₂, Functor.rightDerivedFunctorPlusιUnit, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app]
    erw [← Functor.map_comp_assoc,
      Functor.rightDerivedFunctorPlusCompIso_fac_app,
      Functor.rightDerivedFunctorPlusCompUnit_app, Functor.map_comp]
    simp only [Category.assoc]
    erw [G.rightDerivedFunctorPlusCompatibility.hom.naturality_assoc]
    dsimp only [Functor.comp_map]
    erw [reassoc_of% (CategoryTheory.derivedComplexUnitCompatibility.2.2.2 G
      (F.mapHomotopyCategoryPlus.obj L))]
    erw [← G.rightDerivedFunctor.map_comp,
      CategoryTheory.derivedComplexUnitCompatibility.2.2.2 F L,
      reassoc_of% (CategoryTheory.derivedComplexUnitCompatibility.2.2.2 (F ⋙ G) L)]
    have hu : (F ⋙ G).rightDerivedFunctorUnit.app L.obj ≫
        (Functor.rightDerivedFunctorCompIso F G).hom.app (DerivedCategory.Qh.obj L.obj) =
      (Functor.rightDerivedFunctorCompUnit F G).app L.obj := by
      simp [Functor.rightDerivedFunctorCompIso]
    erw [hu]
    simp only [Functor.rightDerivedFunctorCompUnit, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.id_comp, Category.comp_id,
      Functor.mapHomotopyCategoryCompIso_refl_inv_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
    rfl
  exact congr_app ht K

theorem derived_nat_compat
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [EnoughInjectives C] [HasKInjectiveResolutions C]
    {F G : C ⥤ D} [F.Additive] [G.Additive] (e : F ≅ G)
    (K : DerivedCategory.Plus C) :
    DerivedCategory.Plus.ι.map ((Functor.rightDerivedFunctorPlusNatIso e).hom.app K) ≫
        G.rightDerivedFunctorPlusCompatibility.hom.app K =
      F.rightDerivedFunctorPlusCompatibility.hom.app K ≫
        (Functor.rightDerivedFunctorNatIso e).hom.app K.obj := by
  let τ₁ := Functor.whiskerRight (Functor.rightDerivedFunctorPlusNatIso e).hom
      DerivedCategory.Plus.ι ≫ G.rightDerivedFunctorPlusCompatibility.hom
  let τ₂ := F.rightDerivedFunctorPlusCompatibility.hom ≫
    Functor.whiskerLeft DerivedCategory.Plus.ι (Functor.rightDerivedFunctorNatIso e).hom
  have ht : τ₁ = τ₂ := by
    apply Functor.rightDerived_ext (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι)
      F.rightDerivedFunctorPlusιUnit (HomotopyCategory.Plus.quasiIso C)
    apply NatTrans.ext
    funext L
    simp only [τ₁, τ₂, Functor.rightDerivedFunctorPlusιUnit, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app]
    simp only [Functor.rightDerivedFunctorPlusNatIso]
    erw [← Functor.map_comp_assoc,
      Functor.rightDerivedFunctorPlusNatTrans_app, Functor.map_comp]
    erw [Category.assoc, CategoryTheory.derivedComplexUnitCompatibility.2.2.2 G L,
      reassoc_of% (CategoryTheory.derivedComplexUnitCompatibility.2.2.2 F L)]
    exact (Functor.rightDerivedNatTrans_app F.rightDerivedFunctor G.rightDerivedFunctor
      F.rightDerivedFunctorUnit G.rightDerivedFunctorUnit
      (HomotopyCategory.quasiIso C (.up ℤ))
      (Functor.whiskerRight (NatTrans.mapHomotopyCategory e.hom (.up ℤ)) DerivedCategory.Qh)
      L.obj).symm
  exact congr_app ht K

theorem exact_factor_inv_compat
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [EnoughInjectives C] [HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : DerivedCategory.Plus C) :
    DerivedCategory.Plus.ι.map
        (F.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.inv.app K) ≫
      F.rightDerivedFunctorPlusCompatibility.hom.app K =
    F.rightDerivedFunctorIsoMapDerivedCategory.inv.app K.obj := by
  have ht := congr_app (exact_factor_compat F) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at ht
  apply (cancel_mono (F.rightDerivedFunctorIsoMapDerivedCategory.hom.app K.obj)).mp
  erw [Category.assoc, ← ht, ← Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Iso.inv_hom_id_app]
  rfl

theorem derived_comp_inv_compat
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [EnoughInjectives C] [EnoughInjectives D]
    [HasKInjectiveResolutions C] [HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [F.PreservesInjectiveObjects] [F.PreservesKInjectiveComplexes]
    (K : DerivedCategory.Plus C) :
    DerivedCategory.Plus.ι.map ((Functor.rightDerivedFunctorPlusCompIso F G).inv.app K) ≫
        (F ⋙ G).rightDerivedFunctorPlusCompatibility.hom.app K =
      G.rightDerivedFunctorPlusCompatibility.hom.app (F.rightDerivedFunctorPlus.obj K) ≫
        G.rightDerivedFunctor.map (F.rightDerivedFunctorPlusCompatibility.hom.app K) ≫
        (Functor.rightDerivedFunctorCompIso F G).inv.app K.obj := by
  apply (cancel_epi (DerivedCategory.Plus.ι.map
    ((Functor.rightDerivedFunctorPlusCompIso F G).hom.app K))).mp
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]
  try simp only [Category.assoc]
  erw [reassoc_of% (derived_comp_compat F G K)]
  simp only [Iso.hom_inv_id_app]
  erw [Category.comp_id]

theorem open_iso_compat
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [EnoughInjectives C] [EnoughInjectives D]
    [HasKInjectiveResolutions C] [HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ E) {H : C ⥤ E}
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.PreservesInjectiveObjects] [F.PreservesKInjectiveComplexes]
    (e : F ⋙ G ≅ H) (K : DerivedCategory.Plus C) :
    DerivedCategory.Plus.ι.map
        ((Functor.isoWhiskerRight
            F.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.symm
            G.rightDerivedFunctorPlus ≪≫
          Functor.rightDerivedFunctorPlusCompIso' F G e).hom.app K) ≫
        H.rightDerivedFunctorPlusCompatibility.hom.app K =
      G.rightDerivedFunctorPlusCompatibility.hom.app (F.mapDerivedCategoryPlus.obj K) ≫
        (Functor.isoWhiskerRight F.rightDerivedFunctorIsoMapDerivedCategory.symm
            G.rightDerivedFunctor ≪≫
          Functor.rightDerivedFunctorCompIso' F G e).hom.app K.obj := by
  simp only [Functor.rightDerivedFunctorPlusCompIso', Functor.rightDerivedFunctorCompIso',
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.map_comp, Category.assoc]
  erw [derived_nat_compat e K, reassoc_of% (derived_comp_inv_compat F G K)]
  erw [G.rightDerivedFunctorPlusCompatibility.hom.naturality_assoc]
  erw [← G.rightDerivedFunctor.map_comp_assoc, exact_factor_inv_compat]

theorem compatibility_transport
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [EnoughInjectives C] [EnoughInjectives D]
    [HasKInjectiveResolutions C] [HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ E) {H : C ⥤ E}
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.PreservesInjectiveObjects] [F.PreservesKInjectiveComplexes]
    (e : F ⋙ G ≅ H) (K : DerivedCategory.Plus C)
    (L : DerivedCategory.Plus D) (f : L ⟶ F.mapDerivedCategoryPlus.obj K) :
    G.rightDerivedFunctorPlusCompatibility.hom.app L ≫
        G.rightDerivedFunctor.map (DerivedCategory.Plus.ι.map f) ≫
        (Functor.isoWhiskerRight F.rightDerivedFunctorIsoMapDerivedCategory.symm
            G.rightDerivedFunctor ≪≫
          Functor.rightDerivedFunctorCompIso' F G e).hom.app K.obj ≫
        H.rightDerivedFunctorPlusCompatibility.inv.app K =
      DerivedCategory.Plus.ι.map
        (G.rightDerivedFunctorPlus.map f ≫
          (Functor.isoWhiskerRight
              F.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.symm
              G.rightDerivedFunctorPlus ≪≫
            Functor.rightDerivedFunctorPlusCompIso' F G e).hom.app K) := by
  have hn := G.rightDerivedFunctorPlusCompatibility.hom.naturality f
  simp only [Functor.comp_map] at hn
  erw [← reassoc_of% hn, ← reassoc_of% (open_iso_compat F G e K)]
  simp only [Iso.hom_inv_id_app, Functor.map_comp]
  erw [Category.comp_id]

theorem coefficient_plus_spec (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u}) :
    DerivedCategory.Plus.ι.map
      ((upperStar (Modules P) (openImmersion Y)).mapDerivedCategoryPlus.map
          (((comparisonUpperStar (Modules P) (Line Y)).mapDerivedCategoryPlusSingleFunctor
            0).hom.app (P.twistEtale h (Line Y))) ≫
        ((upperStar (Modules P) (openImmersion Y)).mapDerivedCategoryPlusSingleFunctor
          0).hom.app (P.twist h (Line Y)) ≫
        (DerivedCategory.Plus.singleFunctor (ProSheaves P (Punctured Y)) 0).map
          ((comparisonUpperStarCompUpperStarIso (Modules P) (openImmersion Y)).hom.app
              (P.twistEtale h (Line Y)) ≫
            (comparisonUpperStar (Modules P) (Punctured Y)).map
              (P.twistEtalePullback h (openImmersion Y)))) =
      P.gysinOpenCoefficient h Y := by
  simp only [gysinOpenCoefficient, Functor.map_comp, inclusion_exact_map,
    inclusion_single_map, Functor.ι_map_mapDerivedCategoryPlusSingleFunctor_hom_app]

theorem exact_base_change
    {B B' C C' : Type*} [Category* B] [Category* B'] [Category* C] [Category* C']
    [Abelian B] [Abelian B'] [Abelian C] [Abelian C']
    [HasDerivedCategory B] [HasDerivedCategory B']
    [HasDerivedCategory C] [HasDerivedCategory C']
    [EnoughInjectives B] [EnoughInjectives B']
    {G : B ⥤ C} {G' : B' ⥤ C'} {β : B ⥤ B'} {γ : C ⥤ C'}
    [G.Additive] [G'.Additive] [β.Additive] [γ.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
    [PreservesFiniteLimits β] [PreservesFiniteColimits β]
    [PreservesFiniteLimits γ] [PreservesFiniteColimits γ]
    (e : G ⋙ γ ≅ β ⋙ G') :
    Functor.rightDerivedFunctorPlusBaseChange e.hom ≫
        Functor.whiskerLeft β.mapDerivedCategoryPlus
          G'.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom =
      Functor.whiskerRight G.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom
          γ.mapDerivedCategoryPlus ≫
        (Functor.mapDerivedCategoryPlusSquareIso G γ β G' e).hom := by
  apply Localization.natTrans_ext DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso B)
  intro K
  apply (cancel_epi (γ.mapDerivedCategoryPlus.map
    (G.rightDerivedFunctorPlusUnit.app K))).mp
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  erw [Functor.rightDerivedFunctorPlusBaseChange_fac_app_assoc,
    ← Functor.map_comp_assoc]
  have hu := congr_app G.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus_hom_fac K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hu
  erw [hu]
  apply (cancel_mono
    (G'.mapDerivedCategoryPlus.map (β.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
      G'.mapDerivedCategoryPlusFactorsh.hom.app (β.mapHomotopyCategoryPlus.obj K))).mp
  simp only [Category.assoc]
  erw [Functor.mapDerivedCategoryPlusSquareIso_fac G γ β G' e K]
  erw [G'.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom.naturality_assoc]
  simp only [← G'.mapDerivedCategoryPlus.map_comp_assoc, Iso.inv_hom_id_app]
  have hu' := congr_app G'.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus_hom_fac
    (β.mapHomotopyCategoryPlus.obj K)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hu'
  erw [reassoc_of% hu']
  simp only [Iso.inv_hom_id_app, ← Functor.map_comp_assoc,
    CategoryTheory.Functor.map_id, Category.id_comp]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app,
    Category.comp_id]

section NormalizedBaseChange

variable {B B' C C' E : Type*}
  [Category B] [Category B'] [Category C] [Category C'] [Category E]
  [Abelian B] [Abelian B'] [Abelian C] [Abelian C'] [Abelian E]
  [HasDerivedCategory B] [HasDerivedCategory B'] [HasDerivedCategory C]
  [HasDerivedCategory C'] [HasDerivedCategory E]
  [EnoughInjectives B] [EnoughInjectives B'] [EnoughInjectives C] [EnoughInjectives C']

def normalized_base_change
    {F : B ⥤ E} {F' : B' ⥤ E} {β : B ⥤ B'}
    [F.Additive] [F'.Additive] [β.Additive]
    [PreservesFiniteLimits β] [PreservesFiniteColimits β]
    (e : F ⋙ 𝟭 E ⟶ β ⋙ F') :
    F.rightDerivedFunctorPlus ⟶ β.mapDerivedCategoryPlus ⋙ F'.rightDerivedFunctorPlus :=
  Functor.whiskerLeft F.rightDerivedFunctorPlus
      (Functor.mapDerivedCategoryPlusIdIso E).inv ≫
    Functor.rightDerivedFunctorPlusBaseChange e

theorem normalized_fac
    {F : B ⥤ E} {F' : B' ⥤ E} {β : B ⥤ B'}
    [F.Additive] [F'.Additive] [β.Additive]
    [PreservesFiniteLimits β] [PreservesFiniteColimits β]
    (e : F ⋙ 𝟭 E ⟶ β ⋙ F') (K : HomotopyCategory.Plus B) :
    F.rightDerivedFunctorPlusUnit.app K ≫
        (normalized_base_change e).app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus e).app K) ≫
        F'.rightDerivedFunctorPlusUnit.app (β.mapHomotopyCategoryPlus.obj K) ≫
        F'.rightDerivedFunctorPlus.map (β.mapDerivedCategoryPlusFactorsh.inv.app K) := by
  dsimp only [normalized_base_change, NatTrans.comp_app, Functor.whiskerLeft_app]
  erw [(Functor.mapDerivedCategoryPlusIdIso E).inv.naturality_assoc]
  erw [Functor.rightDerivedFunctorPlusBaseChange_fac_app,
    ← Functor.mapDerivedCategoryPlusIdIso_hom_app_factorsh]
  erw [Iso.inv_hom_id_app_assoc]

theorem normalized_horizontal
    {F H : B ⥤ E} {F' H' : B' ⥤ E} {β : B ⥤ B'}
    [F.Additive] [H.Additive] [F'.Additive] [H'.Additive] [β.Additive]
    [PreservesFiniteLimits β] [PreservesFiniteColimits β]
    (e : F ⋙ 𝟭 E ⟶ β ⋙ F') (e' : H ⋙ 𝟭 E ⟶ β ⋙ H')
    (s : F ⟶ H) (t : F' ⟶ H')
    (he : ∀ X, s.app X ≫ e'.app X = e.app X ≫ t.app (β.obj X)) :
    Functor.rightDerivedFunctorPlusNatTrans s ≫ normalized_base_change e' =
      normalized_base_change e ≫
        Functor.whiskerLeft β.mapDerivedCategoryPlus
          (Functor.rightDerivedFunctorPlusNatTrans t) := by
  apply Functor.rightDerived_ext F.rightDerivedFunctorPlus
    F.rightDerivedFunctorPlusUnit (HomotopyCategory.Plus.quasiIso B)
  apply NatTrans.ext
  funext K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  erw [Functor.rightDerivedFunctorPlusNatTrans_app_assoc, normalized_fac]
  erw [reassoc_of% (normalized_fac e K)]
  have hn := (Functor.rightDerivedFunctorPlusNatTrans t).naturality
    (β.mapDerivedCategoryPlusFactorsh.inv.app K)
  try dsimp only [Functor.comp_map] at hn
  erw [hn, Functor.rightDerivedFunctorPlusNatTrans_app_assoc]
  simp only [← Functor.map_comp_assoc]
  congr 1
  have hk : (NatTrans.mapHomotopyCategoryPlus s).app K ≫
      (NatTrans.mapHomotopyCategoryPlus e').app K =
    (NatTrans.mapHomotopyCategoryPlus e).app K ≫
      (NatTrans.mapHomotopyCategoryPlus t).app (β.mapHomotopyCategoryPlus.obj K) := by
    apply (HomotopyCategory.Plus.ι E).map_injective
    obtain ⟨⟨L⟩, hL⟩ := K
    change (HomotopyCategory.quotient E (.up ℤ)).map _ ≫
        (HomotopyCategory.quotient E (.up ℤ)).map _ =
      (HomotopyCategory.quotient E (.up ℤ)).map _ ≫
        (HomotopyCategory.quotient E (.up ℤ)).map _
    simp only [← Functor.map_comp]
    congr 1
    ext n
    exact he (L.X n)
  exact congrArg DerivedCategory.Plus.Qh.map hk

variable {F : B ⥤ C} {G : C ⥤ E} {H : B ⥤ E}
  {F' : B' ⥤ C'} {G' : C' ⥤ E} {H' : B' ⥤ E}
  {β : B ⥤ B'} {γ : C ⥤ C'}
  [F.Additive] [G.Additive] [H.Additive]
  [F'.Additive] [G'.Additive] [H'.Additive]
  [β.Additive] [γ.Additive]
  [PreservesFiniteLimits β] [PreservesFiniteColimits β]
  [PreservesFiniteLimits γ] [PreservesFiniteColimits γ]
  [F.PreservesInjectiveObjects] [F'.PreservesInjectiveObjects]

theorem normalized_comp (c : F ⋙ G ≅ H) (c' : F' ⋙ G' ≅ H')
    (e₁ : F ⋙ γ ⟶ β ⋙ F') (e₂ : G ⋙ 𝟭 E ⟶ γ ⋙ G')
    (e : H ⋙ 𝟭 E ⟶ β ⋙ H')
    (he : ∀ X, c.inv.app X ≫ e₂.app (F.obj X) ≫ G'.map (e₁.app X) =
      e.app X ≫ c'.inv.app (β.obj X)) (K : DerivedCategory.Plus B) :
    (normalized_base_change e).app K ≫
        (Functor.rightDerivedFunctorPlusCompIso' F' G' c').inv.app
          (β.mapDerivedCategoryPlus.obj K) =
      (Functor.rightDerivedFunctorPlusCompIso' F G c).inv.app K ≫
        (normalized_base_change e₂).app (F.rightDerivedFunctorPlus.obj K) ≫
        G'.rightDerivedFunctorPlus.map
          ((Functor.rightDerivedFunctorPlusBaseChange e₁).app K) := by
  have hb := Functor.rightDerivedFunctorPlusBaseChange_comp c c' e₁ e₂ e he K
  dsimp only [normalized_base_change, NatTrans.comp_app, Functor.whiskerLeft_app]
  symm
  have hn := (Functor.mapDerivedCategoryPlusIdIso E).inv.naturality
    ((Functor.rightDerivedFunctorPlusCompIso' F G c).inv.app K)
  simp only [Functor.id_map] at hn
  simp only [Category.assoc]
  erw [reassoc_of% hn]
  exact congrArg (fun z ↦ (Functor.mapDerivedCategoryPlusIdIso E).inv.app
    (H.rightDerivedFunctorPlus.obj K) ≫ z) hb

variable [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits F'] [PreservesFiniteColimits F']

theorem exact_open_base_change (c : F ⋙ G ≅ H) (c' : F' ⋙ G' ≅ H')
    (e₁ : F ⋙ γ ≅ β ⋙ F') (e₂ : G ⋙ 𝟭 E ⟶ γ ⋙ G')
    (e : H ⋙ 𝟭 E ⟶ β ⋙ H')
    (he : ∀ X, c.inv.app X ≫ e₂.app (F.obj X) ≫ G'.map (e₁.hom.app X) =
      e.app X ≫ c'.inv.app (β.obj X)) (K : DerivedCategory.Plus B) :
    (normalized_base_change e₂).app (F.mapDerivedCategoryPlus.obj K) ≫
        G'.rightDerivedFunctorPlus.map
          ((Functor.mapDerivedCategoryPlusSquareIso F γ β F' e₁).hom.app K) ≫
        (Functor.isoWhiskerRight
            F'.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.symm
            G'.rightDerivedFunctorPlus ≪≫
          Functor.rightDerivedFunctorPlusCompIso' F' G' c').hom.app
            (β.mapDerivedCategoryPlus.obj K) =
      (Functor.isoWhiskerRight
          F.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.symm
          G.rightDerivedFunctorPlus ≪≫
        Functor.rightDerivedFunctorPlusCompIso' F G c).hom.app K ≫
        (normalized_base_change e).app K := by
  let d := Functor.rightDerivedFunctorPlusCompIso' F G c
  let d' := Functor.rightDerivedFunctorPlusCompIso' F' G' c'
  let q := Functor.mapDerivedCategoryPlusSquareIso F γ β F' e₁
  have hb := normalized_comp c c' e₁.hom e₂ e he K
  have hx := congr_app (exact_base_change e₁) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hx
  have hxi : γ.mapDerivedCategoryPlus.map
        (F.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.inv.app K) ≫
      (Functor.rightDerivedFunctorPlusBaseChange e₁.hom).app K =
      q.hom.app K ≫ F'.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.inv.app
        (β.mapDerivedCategoryPlus.obj K) := by
    apply (cancel_mono (F'.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom.app
      (β.mapDerivedCategoryPlus.obj K))).mp
    simp only [Category.assoc, Iso.inv_hom_id_app]
    erw [hx, ← γ.mapDerivedCategoryPlus.map_comp_assoc, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
    dsimp only [q]
    erw [Category.comp_id]
  have hn := (normalized_base_change e₂).naturality
    (F.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.inv.app K)
  simp only [Functor.comp_map] at hn
  have hbc : (normalized_base_change e₂).app (F.rightDerivedFunctorPlus.obj K) ≫
        G'.rightDerivedFunctorPlus.map
          ((Functor.rightDerivedFunctorPlusBaseChange e₁.hom).app K) ≫
        d'.hom.app (β.mapDerivedCategoryPlus.obj K) =
      d.hom.app K ≫ (normalized_base_change e).app K := by
    apply (cancel_epi (d.inv.app K)).mp
    try simp only [Iso.inv_hom_id_app_assoc]
    erw [← reassoc_of% hb]
    dsimp only [d']
    erw [Iso.inv_hom_id_app, Category.comp_id]
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.whiskerRight_app, Category.assoc]
  erw [← G'.rightDerivedFunctorPlus.map_comp_assoc, ← hxi]
  erw [G'.rightDerivedFunctorPlus.map_comp_assoc, ← reassoc_of% hn]
  erw [hbc]

end NormalizedBaseChange

theorem complement_derived_square (P : PurityFiniteSetting.{u}) (X : Scheme.{u})
    (U V : Scheme.Etale X) (eU : U ≅ V)
    (K : DerivedCategory.Plus (EtSheaves P X)) :
    (Functor.rightDerivedFunctorPlusNatIso
        (F := sheafToPresheaf X.smallEtaleTopology (Modules P) ⋙
          (evaluation _ _).obj (op U))
        (G := sheafToPresheaf X.smallEtaleTopology (Modules P) ⋙
          (evaluation _ _).obj (op V))
        ((sheafSections X.smallEtaleTopology (Modules P)).mapIso eU.op).symm).hom.app K ≫
      (finiteComparisonSection X P.Coefficient V).app K =
    (finiteComparisonSection X P.Coefficient U).app K ≫
      (Functor.rightDerivedFunctorPlusNatIso
        (F := sheafToPresheaf (Scheme.ProEt.topology X) (Modules P) ⋙
          (evaluation _ _).obj (op ((Scheme.toProEt X).obj U)))
        (G := sheafToPresheaf (Scheme.ProEt.topology X) (Modules P) ⋙
          (evaluation _ _).obj (op ((Scheme.toProEt X).obj V)))
        ((sheafSections (Scheme.ProEt.topology X) (Modules P)).mapIso
          ((Scheme.toProEt X).mapIso eU).op).symm).hom.app ((nuPlus P X).obj K) := by
  have ht := normalized_horizontal
    (finiteComparisonSectionUnit X P.Coefficient U)
    (finiteComparisonSectionUnit X P.Coefficient V)
    (((sheafSections X.smallEtaleTopology (Modules P)).mapIso eU.op).symm.hom)
    (((sheafSections (Scheme.ProEt.topology X) (Modules P)).mapIso
      ((Scheme.toProEt X).mapIso eU).op).symm.hom)
    (by
      intro F
      exact ((comparisonAdjunction (Modules P) X).unit.app F).hom.naturality eU.inv.op)
  simpa only [normalized_base_change, finiteComparisonSection,
    Functor.rightDerivedFunctorPlusNatIso, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.isoWhiskerLeft_inv,
    Functor.rightUnitor_inv_app, Category.id_comp] using congr_app ht K

theorem complement_hyper_square (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (D : OrientationSupportData P h Y) (M : CoordinateBoundaryModel P Y)
    (K : DerivedCategory.Plus (EtSheaves P (Line Y))) :
    (finiteComparisonSectionHypercohomology (Line Y) P.Coefficient
        (Scheme.Etale.mk (openImmersion Y)) 1).app K ≫
      (complementSectionsIso P (zeroSection Y) (openImmersion Y)
        D.comparison.complement 1).hom.app ((nuPlus P (Line Y)).obj K) =
    (Functor.isoWhiskerRight
      (Functor.rightDerivedFunctorPlusNatIso
        (F := sheafToPresheaf (Line Y).smallEtaleTopology (Modules P) ⋙
          (evaluation _ _).obj (op (Scheme.Etale.mk (openImmersion Y))))
        (G := sheafToPresheaf (Line Y).smallEtaleTopology (Modules P) ⋙
          (evaluation _ _).obj (op (Scheme.Etale.mk (zeroSection Y).openComplement.ι)))
        ((sheafSections (Line Y).smallEtaleTopology (Modules P)).mapIso
          M.complementIso.op).symm)
      (DerivedCategory.Plus.homologyFunctor (Modules P) 1)).hom.app K ≫
      (finiteComparisonSectionHypercohomology (Line Y) P.Coefficient
        (Scheme.Etale.mk (zeroSection Y).openComplement.ι) 1).app K := by
  have he : D.comparison.complement =
      (Scheme.toProEt (Line Y)).mapIso M.complementIso := by
    apply Iso.ext
    apply MorphismProperty.Over.Hom.ext
    apply (cancel_mono (zeroSection Y).openComplement.ι).mp
    exact (MorphismProperty.Over.w D.comparison.complement.hom).trans
      (MorphismProperty.Over.w
        ((Scheme.toProEt (Line Y)).mapIso M.complementIso).hom).symm
  have ht := congrArg ((DerivedCategory.Plus.homologyFunctor (Modules P) 1).map)
    (complement_derived_square P (Line Y) _ _ M.complementIso K)
  simpa only [he, finiteComparisonSectionHypercohomology, complementSectionsIso,
    Functor.map_comp, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    NatTrans.comp_app, Functor.associator_hom_app, Functor.whiskerLeft_app,
    Category.comp_id, id_eq, Sheaf.sectionHypercohomologyFunctor] using ht.symm

def pro_open_plus (P : PurityFiniteSetting.{u})
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (upperStar (Modules P) j).mapDerivedCategoryPlus ⋙
        (globalSectionsFunctor (Modules P) U).rightDerivedFunctorPlus ≅
      (sectionsFunctor (Modules P) (Scheme.ProEt.mk j)).rightDerivedFunctorPlus :=
  letI := (openImmersionLowerShriekUpperStarAdjunction (Modules P)
    j).preservesInjectiveObjects_of_preservesFiniteLimits
  Functor.isoWhiskerRight
      (upperStar (Modules P) j).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.symm
      (globalSectionsFunctor (Modules P) U).rightDerivedFunctorPlus ≪≫
    Functor.rightDerivedFunctorPlusCompIso' (upperStar (Modules P) j)
      (globalSectionsFunctor (Modules P) U) (openSectionsIso P j)

theorem open_derived_square (P : PurityFiniteSetting.{u})
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (K : DerivedCategory.Plus (EtSheaves P X)) :
    (finiteComparisonSection U P.Coefficient (Scheme.Etale.mk (𝟙 U))).app
        ((Etale.upperStar (Modules P) j).mapDerivedCategoryPlus.obj K) ≫
      (globalSectionsFunctor (Modules P) U).rightDerivedFunctorPlus.map
        ((Functor.mapDerivedCategoryPlusSquareIso
          (Etale.upperStar (Modules P) j) (comparisonUpperStar (Modules P) U)
          (comparisonUpperStar (Modules P) X) (upperStar (Modules P) j)
          (comparisonUpperStarCompUpperStarIso (Modules P) j).symm).hom.app K) ≫
      (pro_open_plus P j).hom.app ((nuPlus P X).obj K) =
    (P.coordinateOpenDerivedIso j).hom.app K ≫
      (finiteComparisonSection X P.Coefficient (Scheme.Etale.mk j)).app K := by
  let := (Etale.openImmersionLowerShriekUpperStarAdjunction (Modules P)
    j).preservesInjectiveObjects_of_preservesFiniteLimits
  let := (openImmersionLowerShriekUpperStarAdjunction (Modules P)
    j).preservesInjectiveObjects_of_preservesFiniteLimits
  have ht := exact_open_base_change (P.coordinateOpenSectionsIso j) (openSectionsIso P j)
    (comparisonUpperStarCompUpperStarIso (Modules P) j).symm
    (finiteComparisonSectionUnit U P.Coefficient (Scheme.Etale.mk (𝟙 U)))
    (finiteComparisonSectionUnit X P.Coefficient (Scheme.Etale.mk j))
    (underived_open_square P j) K
  simpa only [normalized_base_change, finiteComparisonSection, pro_open_plus,
    coordinateOpenDerivedIso, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.rightUnitor_inv_app, Functor.isoWhiskerLeft_inv, Category.id_comp] using ht

set_option maxRecDepth 2048 in
set_option maxHeartbeats 800000 in
-- Derived-category mate normalization needs the expanded heartbeat budget.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- The coefficient comparison crosses several derived single-complex constructions.
theorem coefficient_plus_inverse (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k)) (D : OrientationSupportData P h Y) :
    let W := Etale.upperStar (Modules P) (openImmersion Y)
    let V := upperStar (Modules P) (openImmersion Y)
    let N := comparisonUpperStar (Modules P) (Line Y)
    let N' := comparisonUpperStar (Modules P) (Punctured Y)
    let e := comparisonUpperStarCompUpperStarIso (Modules P) (openImmersion Y)
    let S := Functor.mapDerivedCategoryPlusSquareIso W N' N V e.symm
    let t := P.twistEtalePullback h (openImmersion Y)
    let := P.isIso_twistEtalePullback h (openImmersion Y)
      (P.exponent_isUnit (Line Y) (lineProjection Y ≫ a))
    let b := (DerivedCategory.Plus.singleFunctor _ 0).map (inv t) ≫
      (W.mapDerivedCategoryPlusSingleFunctor 0).inv.app (P.twistEtale h (Line Y))
    let f := (N'.mapDerivedCategoryPlusSingleFunctor 0).inv.app
        (P.twistEtale h (Punctured Y)) ≫
      N'.mapDerivedCategoryPlus.map b ≫ S.hom.app (P.coordinateEtaleInput h (Line Y))
    DerivedCategory.Plus.ι.map f = D.openCoefficient.inv := by
  let W := Etale.upperStar (Modules P) (openImmersion Y)
  let V := upperStar (Modules P) (openImmersion Y)
  let N := comparisonUpperStar (Modules P) (Line Y)
  let N' := comparisonUpperStar (Modules P) (Punctured Y)
  let e := comparisonUpperStarCompUpperStarIso (Modules P) (openImmersion Y)
  let S := Functor.mapDerivedCategoryPlusSquareIso W N' N V e.symm
  let t := P.twistEtalePullback h (openImmersion Y)
  let := P.isIso_twistEtalePullback h (openImmersion Y)
    (P.exponent_isUnit (Line Y) (lineProjection Y ≫ a))
  let K := P.coordinateEtaleInput h (Line Y)
  let b := (DerivedCategory.Plus.singleFunctor _ 0).map (inv t) ≫
    (W.mapDerivedCategoryPlusSingleFunctor 0).inv.app (P.twistEtale h (Line Y))
  let f := (N'.mapDerivedCategoryPlusSingleFunctor 0).inv.app
      (P.twistEtale h (Punctured Y)) ≫
    N'.mapDerivedCategoryPlus.map b ≫ S.hom.app K
  let c := V.mapDerivedCategoryPlus.map
      ((N.mapDerivedCategoryPlusSingleFunctor 0).hom.app (P.twistEtale h (Line Y))) ≫
    (V.mapDerivedCategoryPlusSingleFunctor 0).hom.app (P.twist h (Line Y)) ≫
    (DerivedCategory.Plus.singleFunctor _ 0).map
      (e.hom.app (P.twistEtale h (Line Y)) ≫ N'.map t)
  have hs := plus_square_single W N' N V e.symm (P.twistEtale h (Line Y))
  have hc : S.hom.app K ≫ c =
      N'.mapDerivedCategoryPlus.map
        ((W.mapDerivedCategoryPlusSingleFunctor 0).hom.app (P.twistEtale h (Line Y))) ≫
      (N'.mapDerivedCategoryPlusSingleFunctor 0).hom.app
        (W.obj (P.twistEtale h (Line Y))) ≫
      (DerivedCategory.Plus.singleFunctor _ 0).map (N'.map t) := by
    dsimp only [c, K, coordinateEtaleInput, twist] at ⊢
    erw [Functor.map_comp]
    try simp only [Category.assoc]
    erw [reassoc_of% hs]
    erw [← Functor.map_comp_assoc, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
  have hf : f ≫ c = 𝟙 _ := by
    dsimp only [f]
    simp only [Category.assoc]
    erw [hc]
    have hw : N'.mapDerivedCategoryPlus.map
          ((W.mapDerivedCategoryPlusSingleFunctor 0).inv.app (P.twistEtale h (Line Y))) ≫
        N'.mapDerivedCategoryPlus.map
          ((W.mapDerivedCategoryPlusSingleFunctor 0).hom.app (P.twistEtale h (Line Y))) =
        𝟙 _ := by
      erw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
    dsimp only [b, K, coordinateEtaleInput]
    erw [N'.mapDerivedCategoryPlus.map_comp]
    try simp only [Category.assoc]
    erw [reassoc_of% hw]
    erw [(N'.mapDerivedCategoryPlusSingleFunctor 0).hom.naturality_assoc
      ((inv t))]
    simp only [Functor.comp_map, Iso.inv_hom_id_app_assoc]
    erw [← Functor.map_comp, ← N'.map_comp, IsIso.inv_hom_id,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    rfl
  change DerivedCategory.Plus.ι.map f = D.openCoefficient.inv
  apply (cancel_mono D.openCoefficient.hom).mp
  erw [Iso.inv_hom_id, D.openCoefficient_spec, ← coefficient_plus_spec P h Y]
  change DerivedCategory.Plus.ι.map f ≫ DerivedCategory.Plus.ι.map c = 𝟙 _
  erw [← Functor.map_comp, hf, CategoryTheory.Functor.map_id]



end WeilConjectures.PurityFiniteSetting
