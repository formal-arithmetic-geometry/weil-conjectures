/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleProEtaleCoefficientTransport
public import WeilConjectures.SecSmoothPurity.ProperScalarCounitSquare
public import WeilConjectures.AlgebraicGeometry.FiniteRealizationRestrictionCube
import all WeilConjectures.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange
import all WeilConjectures.AlgebraicGeometry.FiniteRealizationRestrictionCube
import WeilConjectures.AlgebraicGeometry.SfIntrinsicDirectImageUnitNormalization
import WeilConjectures.AlgebraicGeometry.ProEtaleFixedScalarRestrictionUnitNormalization

/-! # Scalar restriction and the recorded direct-image presentation

Source: Stacks Tags 00YV, 03D3, 0D6E, 0D6J and 07A6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Functor
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.CoefficientCompatibility

attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  sfIntrinsicModuleEquivalence directImagePresentation
attribute [local implicit_reducible] proEtaleConstantRingMap scalarExtensionFunctor
  sfIntrinsicDerivedEquivalence Equivalence.mapDerivedCategory Functor.mapHomologicalComplex

private theorem roundtrip
    {C D : Type*} [Category C] [Category D]
    {L L' : C ⥤ D} {R R' : D ⥤ C}
    (a : L ⊣ R) (b : L' ⊣ R') (d : R ≅ R') :
    (a.ofNatIsoLeft ((a.ofNatIsoRight d).leftAdjointUniq b)).rightAdjointUniq b = d := by
  let e := (a.ofNatIsoRight d).leftAdjointUniq b
  apply Iso.ext
  ext N
  apply (b.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_symm_rightAdjointUniq_hom_app]
  simp only [Adjunction.ofNatIsoLeft_counit, whiskerLeft_app, NatTrans.comp_app]
  have h := Adjunction.leftAdjointUniq_hom_app_counit (a.ofNatIsoRight d) b N
  simp only [Adjunction.ofNatIsoRight_counit, whiskerRight_app, NatTrans.comp_app] at h
  rw [Adjunction.homEquiv_counit]
  have hn := e.hom.naturality (d.hom.app N)
  apply (cancel_epi (e.hom.app (R.obj N))).mp
  rw [← reassoc_of% hn, h]
  simp only [← L.map_comp_assoc, Iso.hom_inv_id_app, L.map_id, Category.id_comp,
    e, Iso.hom_inv_id_app_assoc]

private theorem directImageModel_eq (A : Type u) [CommRing A] [Finite A]
    {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    (((proEtaleConstantRingAdjunction A g).ofNatIsoLeft
        ((openSquarePullbackModel_existsUnique A g).exists.choose)).rightAdjointUniq
      (sfIntrinsicConstantModuleAdjunction g A)) = openSquare_directImageModel A g := by
  let a := proEtaleConstantRingAdjunction A g
  let b := sfIntrinsicConstantModuleAdjunction g A
  let d := openSquare_directImageModel A g
  let e := (a.ofNatIsoRight d).leftAdjointUniq b
  have he : (openSquarePullbackModel_existsUnique A g).exists.choose = e := by
    apply (openSquarePullbackModel_existsUnique A g).unique
      (openSquarePullbackModel_existsUnique A g).exists.choose_spec
    intro M V s
    have h := (a.ofNatIsoRight d).unit_leftAdjointUniq_hom_app b M
    have hv := congrArg (fun z ↦ z.val.app (Opposite.op V) s) h
    change (e.hom.app M).val.app (Opposite.op ((proEtaleBaseChange g).obj V))
      (((proEtaleConstantRingAdjunction A g).unit.app M).val.app (Opposite.op V) s) =
        ((sfIntrinsicConstantModuleAdjunction g A).unit.app M).val.app (Opposite.op V) s
      at hv
    exact hv
  rw [he]
  exact roundtrip a b d

private noncomputable def unitQNat
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] :
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor where
  app := F.rightDerivedFunctorUnitQ
  naturality := fun _ _ f ↦ F.rightDerivedFunctorUnitQ_naturality f

private theorem rightDerived_natIso_unitQ
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    {F G : C ⥤ D} [F.Additive] [G.Additive] (e : F ≅ G)
    (K : CochainComplex C ℤ) :
    F.rightDerivedFunctorUnitQ K ≫ (Functor.rightDerivedFunctorNatIso e).hom.app
        (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app K) ≫
        G.rightDerivedFunctorUnitQ K := by
  let a := unitQNat F ≫ Functor.whiskerLeft DerivedCategory.Q
    (Functor.rightDerivedFunctorNatIso e).hom
  let b := Functor.whiskerRight (NatIso.mapHomologicalComplex e (.up ℤ)).hom
    DerivedCategory.Q ≫ unitQNat G
  have hi (I : CochainComplex C ℤ) [I.IsKInjective] : a.app I = b.app I := by
    dsimp only [a, b, unitQNat, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app]
    rw [F.rightDerivedFunctorUnitQ_eq, G.rightDerivedFunctorUnitQ_eq]
    apply (cancel_mono (G.rightDerivedFunctorObjQIso I).hom).mp
    rw [Category.assoc]
    change (F.rightDerivedFunctorObjQIso I).inv ≫
        (Functor.rightDerivedFunctorNatTrans e.hom).app (DerivedCategory.Q.obj I) ≫
        (G.rightDerivedFunctorObjQIso I).hom = _
    rw [Functor.rightDerivedFunctorNatTrans_app_Q_obj]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
    rfl
  have hab : a = b := by
    ext J
    obtain ⟨I, _, j, _, _⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective J
    apply (cancel_mono (G.rightDerivedFunctor.map (DerivedCategory.Q.map j))).mp
    erw [← a.naturality, ← b.naturality, hi I]
  exact congr_app hab K


private theorem change_target_normalization
    {C D C' D' : Type*}
    [Category C] [Category D] [Category C'] [Category D']
    [Abelian C] [Abelian D] [Abelian C'] [Abelian D']
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory C'] [HasDerivedCategory D']
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions C']
    (F : C ⥤ D) (G H : C' ⥤ D') (x : C ⥤ C') (y : D ⥤ D')
    [F.Additive] [G.Additive] [H.Additive] [x.Additive] [y.Additive]
    [Limits.PreservesFiniteLimits x] [Limits.PreservesFiniteColimits x]
    [Limits.PreservesFiniteLimits y] [Limits.PreservesFiniteColimits y]
    (c : x ⋙ G ≅ F ⋙ y)
    (b : x.mapDerivedCategory ⋙ G.rightDerivedFunctor ≅
      F.rightDerivedFunctor ⋙ y.mapDerivedCategory)
    (d : H ≅ G)
    (hb : MixedDerivedCube.unitNormalized F G x y
      x.mapDerivedCategory y.mapDerivedCategory
      x.mapDerivedCategoryFactors y.mapDerivedCategoryFactors c.inv b.inv) :
    MixedDerivedCube.unitNormalized F H x y
      x.mapDerivedCategory y.mapDerivedCategory
      x.mapDerivedCategoryFactors y.mapDerivedCategoryFactors
      (Functor.isoWhiskerLeft x d ≪≫ c).inv
      (Functor.isoWhiskerLeft x.mapDerivedCategory
        (Functor.rightDerivedFunctorNatIso d) ≪≫ b).inv := by
  intro I
  simp only [Iso.trans_inv, NatTrans.comp_app, isoWhiskerLeft_inv, whiskerLeft_app,
    NatTrans.mapHomologicalComplex_comp, Functor.map_comp, Category.assoc]
  have hn := (Functor.rightDerivedFunctorNatIso d).inv.naturality
    (x.mapDerivedCategoryFactors.hom.app I)
  dsimp only [Functor.comp_obj] at hn
  rw [← hn, reassoc_of% hb I]
  have hu := rightDerived_natIso_unitQ d.symm
    ((x.mapHomologicalComplex (.up ℤ)).obj I)
  change G.rightDerivedFunctorUnitQ _ ≫
      (Functor.rightDerivedFunctorNatIso d).inv.app _ = _ at hu
  rw [hu]
  rfl


private def ordinaryImageRestriction
    {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (g : Z ⟶ Y) :=
  proEtaleRingRestrictionDirectImage g
    (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
    (proEtaleConstantRing Z A) (proEtaleConstantRing Z B)
    (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := Z) φ)
    (proEtaleConstantRingComparison g A) (proEtaleConstantRingComparison g B)
    (proEtaleConstantInverseImageMap_naturality g
      (CommRingCat.ofHom (uliftRingHom φ))).symm

private theorem ordinary_restriction_model
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    ordinaryImageRestriction φ g =
      isoWhiskerRight (openSquare_directImageModel B g)
          (proEtaleCoefficientRestrictScalars Y φ) ≪≫
        proEtaleCoefficientDirectImageComparison g φ ≪≫
        isoWhiskerLeft (proEtaleCoefficientRestrictScalars Z φ)
          (openSquare_directImageModel A g).symm := by
  apply (proEtaleRingRestrictionDirectImage_existsUnique g
    (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
    (proEtaleConstantRing Z A) (proEtaleConstantRing Z B)
    (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := Z) φ)
    (proEtaleConstantRingComparison g A) (proEtaleConstantRingComparison g B)
    (proEtaleConstantInverseImageMap_naturality g
      (CommRingCat.ofHom (uliftRingHom φ))).symm).unique
    (Classical.choose_spec (proEtaleRingRestrictionDirectImage_existsUnique g
      (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
      (proEtaleConstantRing Z A) (proEtaleConstantRing Z B)
      (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := Z) φ)
      (proEtaleConstantRingComparison g A) (proEtaleConstantRingComparison g B)
      (proEtaleConstantInverseImageMap_naturality g
        (CommRingCat.ofHom (uliftRingHom φ))).symm)).1
  intro M V x
  change ((proEtaleCoefficientDirectImageComparison g φ).hom.app M).val.app V x = x
  exact (proEtaleCoefficientDirectImageComparison_existsUnique g φ).choose_spec.1 M V x

private def ordinaryPresentation (A : Type u) [CommRing A] [Finite A]
    {Z Y : Scheme.{u}} (g : Z ⟶ Y) :=
  isoWhiskerLeft (sfIntrinsicModuleEquivalence Z A).functor
    (openSquare_directImageModel A g) ≪≫ sfIntrinsicDirectImageComparison g A

private theorem presentation_inv_normalized (A : Type u) [CommRing A] [Finite A]
    {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    MixedDerivedCube.unitNormalized
      (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g)
      (proEtaleConstantRingPushforward A g)
      (sfIntrinsicModuleEquivalence Z A).functor
      (sfIntrinsicModuleEquivalence Y A).functor
      (sfIntrinsicDerivedEquivalence Z A).functor
      (sfIntrinsicDerivedEquivalence Y A).functor
      (sfIntrinsicModuleEquivalence Z A).functor.mapDerivedCategoryFactors
      (sfIntrinsicModuleEquivalence Y A).functor.mapDerivedCategoryFactors
      (ordinaryPresentation A g).inv (directImagePresentation A g).inv := by
  unfold directImagePresentation
  rw [directImageModel_eq]
  exact change_target_normalization _ _ _ _ _
    (sfIntrinsicDirectImageComparison g A)
    (sfIntrinsicDerivedDirectImageComparison g A) (openSquare_directImageModel A g)
    (sfIntrinsicDerivedDirectImageComparison_inv_unitQ_factors A g)

private theorem ring_restriction_normalized
    {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    MixedDerivedCube.unitNormalized
      (proEtaleConstantRingPushforward B g) (proEtaleConstantRingPushforward A g)
      (proEtaleCoefficientRestrictScalars Z φ) (proEtaleCoefficientRestrictScalars Y φ)
      (scalarRestriction φ Z) (scalarRestriction φ Y)
      (proEtaleCoefficientRestrictScalars Z φ).mapDerivedCategoryFactors
      (proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategoryFactors
      (ordinaryImageRestriction φ g).hom (directImageScalarRestrictionIso φ g).inv := by
  exact (Classical.choose_spec
    (proEtaleRingRestrictionDerivedDirectImage_existsUnique g
      (proEtaleConstantRing Y A) (proEtaleConstantRing Y B)
      (proEtaleConstantRing Z A) (proEtaleConstantRing Z B)
      (proEtaleConstantRingMap (T := Y) φ) (proEtaleConstantRingMap (T := Z) φ)
      (proEtaleConstantRingComparison g A) (proEtaleConstantRingComparison g B)
      (proEtaleConstantInverseImageMap_naturality g
        (CommRingCat.ofHom (uliftRingHom φ))).symm)).1


/-- The recorded ring-sheaf direct-image presentation commutes with scalar restriction.

Source: Stacks Tags 00YV, 03D3, 0D6E, 0D6J and 07A6; the direct-image
restriction face of the proper-factor normalization.
(blueprint: lem-sp-recorded-restriction-direct-image-normalization).

Proof: identify the ordinary constant-ring direct image with the sectionwise
constant-module direct image using their identity maps on sections. Uniqueness of
the unit-normalized pullback model identifies its recorded right-adjoint comparison
with this identity on sections. The ordinary restriction comparison is the
sectionwise restriction comparison conjugated by those identities, by its unique
section normalization. Naturality of derived units, checked on K-injective
representatives and extended along resolution arrows, transfers the recorded
inverse realization normalization through the model isomorphism. Apply the existing
normalized derived cube to the ordinary restriction/realization cube, using the
transferred presentation normalization and the two scalar-restriction derived-unit
normalizations. Cancel the invertible presentation faces to obtain the displayed
forward cube. No geometric or coefficient mate is inverted except for the specified
restriction isomorphisms. All inputs are unbounded and no properness is needed. -/
theorem recordedRestriction_directImage_cube
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    (L : DerivedCategory
      (Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} (ULift.{u + 1, u} B)))) :
    (directImageConstantPush A g).map
        ((FiniteCompactScalar.realizationRestrictionIso φ Z).hom.app L) ≫
      (directImagePresentation A g).hom.app
        ((@Sheaf.derivedRestrictScalars.{u} Z.ProEt inferInstance
          (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology Z)
          (ULift.{u + 1, u} A) (ULift.{u + 1, u} B) inferInstance inferInstance
          (uliftRingHom φ)).obj L) ≫
      (sfIntrinsicDerivedEquivalence Y A).functor.map
        ((fixedScalarRestrictionDirectImage (uliftRingHom φ) g).hom.app L) =
    (directImageScalarRestrictionIso φ g).hom.app
        ((sfIntrinsicDerivedEquivalence Z B).functor.obj L) ≫
      (scalarRestriction φ Y).map ((directImagePresentation B g).hom.app L) ≫
      (FiniteCompactScalar.realizationRestrictionIso φ Y).hom.app
        ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) g).rightDerivedFunctor.obj L) := by
  let : EssentiallySmall.{u + 1} Z.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let : EssentiallySmall.{u + 1} Y.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let QB := lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) g
  let QA := lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g
  let PB := proEtaleConstantRingPushforward B g
  let PA := proEtaleConstantRingPushforward A g
  let EZB := (sfIntrinsicModuleEquivalence Z B).functor
  let EYB := (sfIntrinsicModuleEquivalence Y B).functor
  let EZA := (sfIntrinsicModuleEquivalence Z A).functor
  let EYA := (sfIntrinsicModuleEquivalence Y A).functor
  let UZ := proEtaleCoefficientRestrictScalars Z φ
  let UY := proEtaleCoefficientRestrictScalars Y φ
  let VZ := sfFixedRestriction.{u, u + 1, u + 1} Z φ
  let VY := sfFixedRestriction.{u, u + 1, u + 1} Y φ
  let cZ := sfRealizationRestriction Z φ
  let cY := sfRealizationRestriction Y φ
  let dA := ordinaryPresentation A g
  let dB := ordinaryPresentation B g
  let h := ordinaryImageRestriction φ g
  let t := fixedScalarRestrictionDirectImageUnderived (uliftRingHom φ) g
  have hs (M) : cY.hom.app (QB.obj M) ≫ EYA.map (t.hom.app M) ≫
      (sfIntrinsicDirectImageComparison g A).inv.app (VZ.obj M) =
      UY.map ((sfIntrinsicDirectImageComparison g B).inv.app M) ≫
        (proEtaleCoefficientDirectImageComparison g φ).hom.app (EZB.obj M) ≫
        (proEtaleConstantModuleDirectImage g A).map (cZ.hom.app M) := by
    apply (cancel_epi (UY.map ((sfIntrinsicDirectImageComparison g B).hom.app M))).mp
    apply (cancel_epi
      ((proEtaleCoefficientDirectImageComparison g φ).inv.app (EZB.obj M))).mp
    apply (cancel_mono ((sfIntrinsicDirectImageComparison g A).hom.app (VZ.obj M))).mp
    simp only [Category.assoc, ← UY.map_comp_assoc, Iso.hom_inv_id_app,
      UY.map_id, Category.id_comp, Iso.inv_hom_id_app]
    rw [show t = Iso.refl _ from fixedScalarRestrictionDirectImageUnderived_eq
      (uliftRingHom φ) g]
    simp only [Iso.refl_hom, NatTrans.id_app, Functor.comp_obj]
    have hh := FiniteCompactScalar.realizationRestriction_ordinary_directImage_cube φ g M
    rw [EYA.map_id]
    apply (cancel_epi
      ((proEtaleCoefficientDirectImageComparison g φ).hom.app (EZB.obj M))).mp
    simpa only [Category.assoc, UY, cY, QB, cZ, EZB, VZ, EYA,
      Functor.map_id, Category.id_comp, Category.comp_id,
      Iso.hom_inv_id_app_assoc] using congrArg
      (fun z ↦ (proEtaleCoefficientDirectImageComparison g φ).hom.app (EZB.obj M) ≫ z)
        hh.symm
  have ho (M) : cY.hom.app (QB.obj M) ≫ EYA.map (t.hom.app M) ≫
      dA.inv.app (VZ.obj M) = UY.map (dB.inv.app M) ≫
        h.hom.app (EZB.obj M) ≫ PA.map (cZ.hom.app M) := by
    simp only [dA, dB, ordinaryPresentation, h, ordinary_restriction_model,
      Iso.trans_inv, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      isoWhiskerLeft_inv, isoWhiskerRight_hom, isoWhiskerLeft_hom,
      whiskerLeft_app, whiskerRight_app, Functor.map_comp, Category.assoc]
    have hcancel :
        UY.map ((openSquare_directImageModel B g).inv.app (EZB.obj M)) ≫
          UY.map ((openSquare_directImageModel B g).hom.app (EZB.obj M)) = 𝟙 _ := by
      rw [← UY.map_comp, Iso.inv_hom_id_app, UY.map_id]
    rw [reassoc_of% hcancel]
    have hn := (openSquare_directImageModel A g).inv.naturality (cZ.hom.app M)
    erw [← hn, reassoc_of% hs M]
    rfl
  have hc := MixedDerivedCube.normalized_cube QB PB EZB EYB PA QA UZ UY VZ VY EZA EYA
    dB.symm h t dA.symm
    (directImagePresentation B g).symm (directImageScalarRestrictionIso φ g).symm
    (fixedScalarRestrictionDirectImage (uliftRingHom φ) g).symm
    (directImagePresentation A g).symm
    (presentation_inv_normalized B g) (ring_restriction_normalized φ g)
    (fixedScalarRestrictionDirectImage_unitQ_factors (uliftRingHom φ) g)
    (presentation_inv_normalized A g) cZ cY ho L
  simp only [Iso.symm_hom] at hc
  rw [FiniteCompactScalar.restriction_eq, FiniteCompactScalar.restriction_eq]
  change PA.rightDerivedFunctor.map
      ((Functor.mapDerivedCategorySquareIso cZ).hom.app L) ≫
    (directImagePresentation A g).hom.app (VZ.mapDerivedCategory.obj L) ≫
    EYA.mapDerivedCategory.map
      ((fixedScalarRestrictionDirectImage (uliftRingHom φ) g).hom.app L) =
    (directImageScalarRestrictionIso φ g).hom.app (EZB.mapDerivedCategory.obj L) ≫
    UY.mapDerivedCategory.map ((directImagePresentation B g).hom.app L) ≫
    (Functor.mapDerivedCategorySquareIso cY).hom.app (QB.rightDerivedFunctor.obj L)
  apply (cancel_epi
    (UY.mapDerivedCategory.map ((directImagePresentation B g).inv.app L) ≫
      (directImageScalarRestrictionIso φ g).inv.app (EZB.mapDerivedCategory.obj L))).mp
  simp only [Category.assoc]
  rw [reassoc_of% hc]
  simp only [← EYA.mapDerivedCategory.map_comp, Iso.inv_hom_id_app,
    Iso.inv_hom_id_app_assoc, Functor.comp_obj, ← UY.mapDerivedCategory.map_comp_assoc]
  erw [EYA.mapDerivedCategory.map_id, UY.mapDerivedCategory.map_id]
  erw [Category.comp_id, Category.id_comp]


end AlgebraicGeometry.ProEtale.CoefficientCompatibility
