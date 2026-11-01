/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
import all WeilConjectures.AlgebraicGeometry.Etale.Origin.EtaleOriginExtensionPullbackCube
import all WeilConjectures.AlgebraicGeometry.Etale.Origin.EtaleOriginRestrictionPullbackCube
import all WeilConjectures.SixFunctors.Finite.Scalar.FiniteScalarPullbackRepresentativeFactorsFactorized
import all WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantOpenSquareExchange
import all WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedScalarRestrictionDirectImage

/-! # Intrinsic scalar/site/inverse-image cube -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2000
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale

open CategoryTheory.Functor WeilConjectures

attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Functor.leftDerivedFunctor
attribute [local implicit_reducible] Equivalence.mapDerivedCategory
  Scheme.sfIntrinsicDerivedEquivalence Functor.mapHomologicalComplex
  scalarExtensionFunctor Scheme.sfIntrinsicPullback reductionSite Scheme.pbcDerivedRestrict

section
universe a b c d va vb vc vd
variable {A : Type a} {B : Type b} {A' : Type c} {B' : Type d}
  [Category.{va} A] [Category.{vb} B] [Category.{vc} A'] [Category.{vd} B']

end

section
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField sfIntrinsicModuleEquivalence
attribute [local implicit_reducible] proEtaleConstantModuleDirectImage
  proEtaleRingModuleDirectImage SheafOfModules.pushforward
  PresheafOfModules.pushforward PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj'


/-- Normalize ordinary pullback by its sectionwise unit equation. This is the
unit-uniqueness argument of FiniteIntrinsicPullbackNormalization, proved here without
its projection-coordinate imports. The equivalence triangle identities identify
the conjugated inverse mate with the unique unit-preserving bridge. -/
private theorem intrinsic_pullback_normalization
    (R : Type u) [CommRing R] [Finite R] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    openSquarePullbackModel R f =
      (Functor.leftUnitor _).symm ≪≫
        Functor.isoWhiskerRight (sfIntrinsicModuleEquivalence Y R).counitIso.symm
          (proEtaleConstantRingPullback R f) ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (sfIntrinsicModuleEquivalence Y R).inverse
          (finiteScalarOrdinaryPullbackComparison R f) := by
  let EX := sfIntrinsicModuleEquivalence X R
  let EY := sfIntrinsicModuleEquivalence Y R
  let a := ProEtale.upperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1} R)) f
  let b := proEtaleConstantRingAdjunction R f
  let d := openSquare_directImageModel R f
  have hd : d = eqToIso (finiteScalarConstantPushforward_eq R f) := by
    exact pushforwardCongr_eq _
  let c := sfIntrinsicDirectImageComparison f R
  let s := finiteScalarOrdinaryPullbackComparison R f
  let e : proEtaleConstantRingPullback R f ≅ sfIntrinsicPullback R f :=
    (Functor.leftUnitor _).symm ≪≫
      Functor.isoWhiskerRight EY.counitIso.symm _ ≪≫
        Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft EY.inverse s
  apply (openSquarePullbackModel_existsUnique R f).unique
    (openSquarePullbackModel_existsUnique R f).exists.choose_spec
  intro M V x
  have hs : (mateEquiv a (b.ofNatIsoRight d) s.hom).natTrans = c.inv := by
    rw [mate_right_iso]
    have h : (mateEquiv a b s.hom).natTrans =
        (c.symm ≪≫ Functor.isoWhiskerLeft EX.functor d.symm).hom := by
      rw [hd]
      unfold s finiteScalarOrdinaryPullbackComparison
      exact congrArg TwoSquare.natTrans ((mateEquiv a b).apply_symm_apply _)
    rw [h]
    apply NatTrans.ext
    funext K
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.assoc,
      Iso.inv_hom_id_app, Category.comp_id, Functor.comp_obj, EX]
  have hu := normalized_inverseMate_unit EY EX a (b.ofNatIsoRight d) c s hs M
  change (b.ofNatIsoRight d).unit.app M ≫ _ =
    (sfIntrinsicConstantModuleAdjunction f R).unit.app M at hu
  rw [Adjunction.ofNatIsoRight_unit] at hu
  have hv := congrArg (fun z ↦ z.val.app (Opposite.op V) x) hu
  simp only [NatTrans.comp_app, SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply] at hv
  change ((e.hom.app M).val.app (Opposite.op ((proEtaleBaseChange f).obj V)))
    (((b.unit.app M).val.app (Opposite.op V)) x) =
      ((sfIntrinsicConstantModuleAdjunction f R).unit.app M).val.app (Opposite.op V) x at hv
  simpa only [e, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.leftUnitor_inv_app, Functor.associator_hom_app, Category.id_comp,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply] using hv

end

private theorem scalar_realization_normalization
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u}) :
    reductionRealizationScalarIso φ T = Scheme.FiniteCompactScalar.realizationScalarIso φ T := by
  apply Iso.ext
  apply (mateEquiv
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology T)
        (RingHom.ulift.{u + 1, u + 1, u, u} φ)))
    (Scheme.pbcDerivedScalarAdjunction
      (Scheme.FiniteCompactScalar.scalarRingMap φ T))).injective
  change (mateEquiv _ _ ((mateEquiv _ _).symm _)) = _
  exact (Equiv.apply_symm_apply _ _).trans (realization_scalar_mate φ T).symm

private theorem ordinary_realization_normalization
    (A : Type u) [CommRing A] [Finite A] {U X : Scheme.{u}} (i : U ⟶ X) :
    Functor.isoWhiskerLeft (sfIntrinsicModuleEquivalence X A).functor
        (openSquarePullbackModel A i) ≪≫
      (sfIntrinsicModuleEquivalence X A).funInvIdAssoc
        (upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) i ⋙
          (sfIntrinsicModuleEquivalence U A).functor) =
      finiteScalarOrdinaryPullbackComparison A i := by
  rw [intrinsic_pullback_normalization]
  apply Iso.ext
  apply NatTrans.ext
  funext M
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.leftUnitor_inv_app, Functor.associator_hom_app,
    Equivalence.funInvIdAssoc_hom_app, Category.id_comp]
  rw [Category.assoc, ← (finiteScalarOrdinaryPullbackComparison A i).hom.naturality]
  dsimp only [Functor.comp_map]
  rw [← Functor.map_comp_assoc, Equivalence.counitIso_functor_comp]
  exact (congrArg (fun z ↦ z ≫ (finiteScalarOrdinaryPullbackComparison A i).hom.app M)
    ((proEtaleConstantRingPullback A i).map_id _)).trans (Category.id_comp _)

private theorem push_realization_normalization
    (A : Type u) [CommRing A] [Finite A] {U X : Scheme.{u}} (i : U ⟶ X) :
    properOriginPushIso A i = Functor.rightDerivedFunctorNatIso
      (eqToIso (finiteScalarConstantPushforward_eq A i)) := by
  unfold properOriginPushIso
  rw [pushforwardCongr_eq]

private theorem pullback_mate_normalization
    (A : Type u) [CommRing A] [Finite A] {U X : Scheme.{u}} (i : U ⟶ X) :
    realization_pullback A i = (finiteScalarPullbackComparison A i).hom := by
  unfold realization_pullback originRealizationPushIso finiteScalarPullbackComparison
  rw [push_realization_normalization]
  rfl

private theorem derived_realization_normalization
    (A : Type u) [CommRing A] [Finite A] {U X : Scheme.{u}} (i : U ⟶ X) :
    (reductionRealizationPullbackIso A i).hom = realization_pullback A i ≫
      Functor.whiskerRight
        (leftDerivedUpperStarIsoMapDerivedCategory
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) i).hom
        (sfIntrinsicDerivedEquivalence U A).functor := by
  let L := upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) i
  let L' := proEtaleRingModulePullback i (proEtaleConstantRing X A)
    (proEtaleConstantRing U A) (proEtaleConstantRingComparison i A)
  let G := (sfIntrinsicModuleEquivalence X A).functor
  let H := (sfIntrinsicModuleEquivalence U A).functor
  let a := upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} A)) i
  let b := proEtaleRingModuleAdjunction i (proEtaleConstantRing X A)
    (proEtaleConstantRing U A) (proEtaleConstantRingComparison i A)
  let s := finiteScalarOrdinaryPullbackComparison A i
  let hg := finiteScalarConstantPushforward_eq A i
  let t := (sfIntrinsicDirectImageComparison i A).symm ≪≫
    isoWhiskerLeft H (eqToIso hg).symm
  let d := (sfIntrinsicDerivedDirectImageComparison i A).symm ≪≫
    isoWhiskerLeft H.mapDerivedCategory (Functor.rightDerivedFunctorNatIso (eqToIso hg)).symm
  have hs : (mateEquiv a b s.hom).natTrans = t.hom := by
    unfold s finiteScalarOrdinaryPullbackComparison
    exact congrArg TwoSquare.natTrans ((mateEquiv a b).apply_symm_apply _)
  have hd := normalization_transport
    (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) i)
    (proEtaleConstantRingPushforward A i) (proEtaleConstantModuleDirectImage i A) G H hg
    (sfIntrinsicDirectImageComparison i A).symm
    (sfIntrinsicDerivedDirectImageComparison i A).symm
    (sfIntrinsicDerivedDirectImageComparison_inv_unitQ_factors A i)
  have he := inverse_mate_localization a b s t d hs hd
  have hα : (finiteScalarPullbackComparison A i).hom ≫
      Functor.whiskerRight L.leftDerivedFunctorIsoMapDerivedCategory.hom H.mapDerivedCategory =
        (Functor.mapDerivedCategorySquareIso s).hom := by
    change ((mateEquiv (derivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) i)
      b.mapDerivedCategoryRightDerivedAdjunction).symm d.hom).natTrans ≫
      Functor.whiskerRight L.leftDerivedFunctorIsoMapDerivedCategory.hom H.mapDerivedCategory = _
    rw [restriction_derived_adj_eq]
    exact (inverse_mate_left_iso a.mapDerivedCategoryRightDerivedAdjunction
      b.mapDerivedCategoryRightDerivedAdjunction
      L.leftDerivedFunctorIsoMapDerivedCategory.symm d.hom).trans he
  rw [pullback_mate_normalization]
  rw [reductionRealizationPullbackIso, ordinary_realization_normalization]
  exact hα.symm

private theorem ordinary_site_normalization
    (A : Type u) [CommRing A] {U X : Scheme.{u}} (i : U ⟶ X) :
    sfComparisonPullbackIso A i =
      comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} (ULift.{u + 1} A)) i := by
  have h : sfToProEtBaseChangeIso i = toProEtCompOverPullbackIso i := by
    ext W
    rfl
  unfold sfComparisonPullbackIso comparisonUpperStarCompUpperStarIso
    sfComparisonDirectImageCompIso lowerStarCompComparisonLowerStarIso
  rw [h]

private theorem site_scalar_normalization
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u})
    (M : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) T) :
    (scalarExtensionFunctor φ T).map
        ((Scheme.FiniteCompactScalar.intrinsicSiteFunctorIso A T).hom.app M) ≫
      (reductionSiteScalarIso φ T).hom.app M =
    (Scheme.FiniteCompactScalar.siteScalarIso φ T).hom.app M ≫
      (Scheme.FiniteCompactScalar.intrinsicSiteFunctorIso B T).hom.app
        ((Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) T).obj M) := by
  unfold Scheme.FiniteCompactScalar.siteScalarIso reductionSiteScalarIso
  rw [scalar_realization_normalization]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc, Iso.inv_hom_id_app,
    scalarExtensionFunctor, scalarExtension, reductionSite]
  erw [Category.comp_id]

private theorem site_pullback_realization_normalization
    (A : Type u) [CommRing A] [Finite A] {U X : Scheme.{u}} (i : U ⟶ X)
    (M : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) X) :
    (proEtaleConstantRingDerivedPullback A i).map
        ((Scheme.FiniteCompactScalar.intrinsicSiteFunctorIso A X).hom.app M) ≫
      (reductionSitePullbackIso A i).hom.app M =
    (originPullback A i).app M ≫
      (Scheme.FiniteCompactScalar.intrinsicSiteFunctorIso A U).hom.app
        ((Etale.ordinaryFinitePullback (ULift.{u + 1, u} A) i).obj M) := by
  have hr := congr_app (derived_realization_normalization A i)
    ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).mapDerivedCategory.obj M)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app] at hr
  rw [origin_pullback_decomposition]
  dsimp only [Etale.ordinaryFinitePullback]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [site_pullback_normalization]
  simp only [reductionSitePullbackIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp]
  rw [hr]
  simp only [Category.assoc]
  rw [sfDerivedComparisonPullbackIso, ordinary_site_normalization]
  simp only [directImageComparisonAmbientPullbackIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.map_comp, Category.assoc,
    Functor.comp_map, Category.id_comp, reductionSite]
  erw [Category.comp_id]

set_option maxHeartbeats 800000 in
-- Normalizing the large derived-functor presentations and pasting their cubes needs extra fuel.
/-- Scalar extension, site comparison and inverse image have the same normalized
composite. Source: blueprint latest, reduction-exceptional proof, Charts, comparison
of sites and coefficients (blueprint: lem-sp-reduction-site-scalar-pullback).

Proof: first work in fixed ModuleCat-valued sheaves. The scalar/site/pullback cube
is etaleProEtale_scalar_pullback_cube. Transport that cube through the intrinsic
module equivalences. The realization scalar arrow is the inverse mate of exact
restriction of scalars, while the realization inverse-image arrow is the derived
section-normalized openSquarePullbackModel. The two restriction squares commute
sectionwise, since both send a section and its coefficient to their identical
pullbacks. Taking their inverse mates and descending exact functors to the derived
categories identifies the transported cube with the displayed equation. Finally
use the exact-to-left-derived ordinary pullback isomorphism on both coefficient
sides. No boundedness, smoothness or choice of orientation is used. -/
theorem reductionSite_scalar_pullback
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {U X : Scheme.{u}} (i : U ⟶ X)
    (L : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) X) :
    (directImageScalarPullbackIso φ i).inv.app ((reductionSite A X).obj L) ≫
        (proEtaleConstantRingDerivedPullback B i).map
          ((reductionSiteScalarIso φ X).hom.app L) ≫
        (reductionSitePullbackIso B i).hom.app
          ((Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) X).obj L) =
      (scalarExtensionFunctor φ U).map ((reductionSitePullbackIso A i).hom.app L) ≫
        (reductionSiteScalarIso φ U).hom.app
          ((Etale.ordinaryFinitePullback (ULift.{u + 1, u} A) i).obj L) ≫
        (reductionSite B U).map
          ((Etale.scalarPullbackIso (RingHom.ulift.{u + 1, u + 1, u, u} φ) i).inv.app L) := by
  let a := RingHom.ulift.{u + 1, u + 1, u, u} φ
  let PA := proEtaleConstantRingDerivedPullback A i
  let PB := proEtaleConstantRingDerivedPullback B i
  let TX := scalarExtensionFunctor φ X
  let TU := scalarExtensionFunctor φ U
  let e (R : Type u) [CommRing R] [Finite R] (T : Scheme.{u}) :=
    Scheme.FiniteCompactScalar.intrinsicSiteFunctorIso R T
  have h := conjugate_cube
    (PB.mapIso ((Scheme.FiniteCompactScalar.siteScalarIso φ X).app L))
    ((directImageScalarPullbackIso φ i).app
      ((finiteCoefficientIntrinsicDerivedComparison X A).obj L))
    ((finiteCoefficientIntrinsicDerivedComparison U B).mapIso
      ((Etale.scalarPullbackIso a i).app L))
    ((Scheme.FiniteCompactScalar.siteScalarIso φ U).app
      ((Etale.ordinaryFinitePullback (ULift.{u + 1, u} A) i).obj L))
    ((originPullback B i).app ((Etale.scalarExtension a X).obj L))
    (TU.map ((originPullback A i).app L))
    (etaleOriginExtensionPullbackCube φ i L)
  simp only [Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv] at h
  have nx₀ := (directImageScalarPullbackIso φ i).inv.naturality ((e A X).hom.app L)
  have nu₀ := (e B U).hom.naturality ((Etale.scalarPullbackIso a i).inv.app L)
  have nu : (finiteCoefficientIntrinsicDerivedComparison U B).map
        ((Etale.scalarPullbackIso a i).inv.app L) ≫
      (Scheme.FiniteCompactScalar.intrinsicSiteFunctorIso B U).hom.app
        ((Etale.ordinaryFinitePullback (ULift.{u + 1, u} B) i).obj
          ((Etale.scalarExtension a X).obj L)) =
      (Scheme.FiniteCompactScalar.intrinsicSiteFunctorIso B U).hom.app
          ((Etale.scalarExtension a U).obj
            ((Etale.ordinaryFinitePullback (ULift.{u + 1, u} A) i).obj L)) ≫
        (reductionSite B U).map ((Etale.scalarPullbackIso a i).inv.app L) := nu₀
  have nx : TU.map (PA.map ((e A X).hom.app L)) ≫
      (directImageScalarPullbackIso φ i).inv.app ((reductionSite A X).obj L) =
      (directImageScalarPullbackIso φ i).inv.app
          ((finiteCoefficientIntrinsicDerivedComparison X A).obj L) ≫
        PB.map (TX.map ((e A X).hom.app L)) := nx₀
  apply (cancel_epi (TU.map (PA.map ((e A X).hom.app L)))).1
  rw [reassoc_of% nx]
  conv_lhs =>
    rw [← PB.map_comp_assoc, site_scalar_normalization, PB.map_comp]
    simp only [Category.assoc]
    rw [site_pullback_realization_normalization]
  conv_rhs =>
    rw [← TU.map_comp_assoc, site_pullback_realization_normalization, TU.map_comp]
    simp only [Category.assoc]
    rw [reassoc_of% (site_scalar_normalization φ U
      ((Etale.ordinaryFinitePullback (ULift.{u + 1, u} A) i).obj L))]
    rw [← nu]
  simpa only [Category.assoc] using
    congrArg (fun z ↦ z ≫ (e B U).hom.app
      ((Etale.ordinaryFinitePullback (ULift.{u + 1, u} B) i).obj
        ((Etale.scalarExtension a X).obj L))) h

end AlgebraicGeometry.ProEtale
