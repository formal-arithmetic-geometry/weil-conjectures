/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
import all WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMate
import all WeilConjectures.AlgebraicGeometry.Etale.EtaleDirectImageScalarComposition
import all WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.EtaleProEtaleCoefficientCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionIdIso

/-! # Scalar compatibility of the normalized identity compactification -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  derivedTensor upperStar lowerStar

private theorem identity_left_scalar
    {C D : Type*} [Category C] [Category D]
    {L R : C ⥤ C} {L' R' : D ⥤ D}
    (a : L ⊣ R) (b : L' ⊣ R') (S : C ⥤ D)
    (l : L ≅ 𝟭 C) (r : R ≅ 𝟭 C) (l' : L' ≅ 𝟭 D) (r' : R' ≅ 𝟭 D)
    (α : L ⋙ S ⟶ S ⋙ L') (χ : R ⋙ S ⟶ S ⋙ R')
    (ha : ∀ X, l.inv.app (R.obj X) ≫ a.counit.app X = r.hom.app X)
    (hb : ∀ Y, l'.inv.app (R'.obj Y) ≫ b.counit.app Y = r'.hom.app Y)
    (hc : ∀ X, α.app (R.obj X) ≫ L'.map (χ.app X) ≫
      b.counit.app (S.obj X) = S.map (a.counit.app X))
    (hr : ∀ X, χ.app X ≫ r'.hom.app (S.obj X) = S.map (r.hom.app X))
    (X : C) : α.app X ≫ l'.hom.app (S.obj X) = S.map (l.hom.app X) := by
  have hh (X : C) : α.app (R.obj X) ≫ l'.hom.app (S.obj (R.obj X)) =
      S.map (l.hom.app (R.obj X)) := by
    apply (cancel_mono (S.map (r.hom.app X))).mp
    conv_lhs => rw [← hr X]
    have hn := l'.hom.naturality (χ.app X)
    simp only [Functor.id_map] at hn
    simp only [Category.assoc]
    rw [← reassoc_of% hn]
    have hb' : l'.hom.app (R'.obj (S.obj X)) ≫ r'.hom.app (S.obj X) =
        b.counit.app (S.obj X) := by
      rw [← hb, Iso.hom_inv_id_app_assoc]
    rw [hb', hc]
    rw [← S.map_comp]
    congr 1
    rw [← ha, Iso.hom_inv_id_app_assoc]
  apply (cancel_epi (S.map (L.map (r.hom.app X)))).mp
  have hn := α.naturality (r.hom.app X)
  simp only [Functor.comp_map, Functor.id_obj] at hn
  rw [← Category.assoc, hn, Category.assoc]
  have hl := l'.hom.naturality (S.map (r.hom.app X))
  simp only [Functor.id_map, Functor.id_obj] at hl
  rw [hl, ← Category.assoc, hh, ← S.map_comp, ← S.map_comp]
  congr 1
  simpa only [Functor.id_map, Functor.id_obj] using (l.hom.naturality (r.hom.app X)).symm

private theorem open_scalar_counit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j]
    (K : DerivedCategoryModule A V) :
    (ExceptionalCoefficients.openIso φ j).hom.app
        ((ordinaryFinitePullback A j).obj K) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.map
        ((scalarPullbackIso φ j).inv.app K) ≫
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} B) j).ofNatIsoRight
          (leftDerivedUpperStarIsoMapDerivedCategory
            (ModuleCat.{u + 1} B) j).symm).counit.app ((scalarExtension φ V).obj K) =
    (scalarExtension φ V).map
      (((derivedOpenImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) j).ofNatIsoRight
          (leftDerivedUpperStarIsoMapDerivedCategory
            (ModuleCat.{u + 1} A) j).symm).counit.app K) := by
  let a := (derivedOpenImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) j).ofNatIsoRight
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j).symm
  let b := (derivedOpenImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} B) j).ofNatIsoRight
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) j).symm
  let x := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars V.smallEtaleTopology φ)
  let v := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars U.smallEtaleTopology φ)
  let α := (mateEquiv x v).symm
    (TwoSquare.mk _ _ _ _ (scalarRestrictionPullbackIso φ j).hom)
  have he : α.natTrans = (scalarPullbackIso φ j).inv := by
    change (ProEtale.scalarPullbackEtaleIsoFromMate φ j).inv = _
    exact congrArg Iso.inv (scalarPullback_eq φ j)
  have h := congrArg TwoSquare.natTrans
    (iterated_mateEquiv_conjugateEquiv_symm a b v x
      (TwoSquare.mk _ _ _ _ (scalarRestrictionPullbackIso φ j).hom))
  change ((mateEquiv a b).symm α).natTrans = _ at h
  change ((mateEquiv a b).symm α).natTrans = (ExceptionalCoefficients.openIso φ j).inv at h
  have hc := mateEquiv_counit_symm a b α K
  change (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.map
      (α.natTrans.app K) ≫ b.counit.app ((scalarExtension φ V).obj K) =
    ((mateEquiv a b).symm α).natTrans.app _ ≫
      (scalarExtension φ V).map (a.counit.app K) at hc
  rw [he, h] at hc
  have hh := congrArg (fun z ↦ (ExceptionalCoefficients.openIso φ j).hom.app
    ((ordinaryFinitePullback A j).obj K) ≫ z) hc
  simpa only [a, b, ordinaryFinitePullback, Category.assoc,
    Iso.hom_inv_id_app_assoc] using hh

private theorem open_identity_counit
    (A : Type (u + 1)) [CommRing A] (S : Scheme.{u})
    (K : DerivedCategoryModule A S) :
    (mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) S).inv.app
        ((ordinaryFinitePullback A (𝟙 S)).obj K) ≫
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) (𝟙 S)).ofNatIsoRight
          (leftDerivedUpperStarIsoMapDerivedCategory
            (ModuleCat.{u + 1} A) (𝟙 S)).symm).counit.app K =
      (leftDerivedUpperStarId (ModuleCat.{u + 1} A) S).hom.app K := by
  let a := openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 S)
  let l := openImmersionLowerShriekId (ModuleCat.{u + 1} A) S
  let r := upperStarId (ModuleCat.{u + 1} A) S
  have hs (M : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) :
      l.inv.app ((upperStar (ModuleCat.{u + 1} A) (𝟙 S)).obj M) ≫
        a.counit.app M = r.hom.app M := by
    have hh := a.leftAdjointUniq_hom_app_counit (Adjunction.id.ofNatIsoRight r.symm) M
    change l.hom.app _ ≫ r.hom.app M = a.counit.app M at hh
    rw [← hh, Iso.inv_hom_id_app_assoc]
  have hd := a.mapDerivedCategoryAdjunction_counit_app_of_iso l r hs K
  let j := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) (𝟙 S)
  have hn := (mapDerivedCategoryOpenImmersionLowerShriekId
    (ModuleCat.{u + 1} A) S).inv.naturality (j.hom.app K)
  simp only [Functor.id_map] at hn
  simp only [Adjunction.ofNatIsoRight_counit, NatTrans.comp_app,
    Functor.whiskerRight_app, Iso.symm_inv,
    ordinaryFinitePullback]
  change _ ≫ (openImmersionLowerShriek (ModuleCat.{u + 1} A) (𝟙 S)).mapDerivedCategory.map
    (j.hom.app K) ≫ _ = _
  rw [← Category.assoc, ← hn, Category.assoc]
  change j.hom.app K ≫
    (Functor.mapDerivedCategoryNatIso l ≪≫ Functor.mapDerivedCategoryIdIso _).inv.app _ ≫
      a.mapDerivedCategoryAdjunction.counit.app K = _
  rw [hd]
  simp only [j, leftDerivedUpperStarIsoMapDerivedCategory, leftDerivedUpperStarId,
    Functor.leftDerivedFunctorNatIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc, Iso.inv_hom_id_app_assoc, r]

private theorem identity_open_scalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (S : Scheme.{u}) (K : DerivedCategoryModule A S) :
    (ExceptionalCoefficients.openIso φ (𝟙 S)).hom.app K ≫
      (mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} B) S).hom.app
        ((scalarExtension φ S).obj K) =
      (scalarExtension φ S).map
        ((mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) S).hom.app K) := by
  apply identity_left_scalar
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) (𝟙 S)).ofNatIsoRight
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) (𝟙 S)).symm)
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} B) (𝟙 S)).ofNatIsoRight
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) (𝟙 S)).symm)
    (scalarExtension φ S)
    (mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) S)
    (leftDerivedUpperStarId (ModuleCat.{u + 1} A) S)
    (mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} B) S)
    (leftDerivedUpperStarId (ModuleCat.{u + 1} B) S)
    (ExceptionalCoefficients.openIso φ (𝟙 S)).hom (scalarPullbackIso φ (𝟙 S)).inv
    (open_identity_counit A S) (open_identity_counit B S)
    (open_scalar_counit φ (𝟙 S))
  intro X
  rw [← (leftDerivedUpperStarId_scalarExtension_normalization φ S).2.2 X,
    Iso.inv_hom_id_app_assoc]

private theorem identity_direct_scalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (S : Scheme.{u}) (K : DerivedCategoryModule A S) :
    (scalarMate φ (𝟙 S)).app K ≫
      (rightDerivedLowerStarIdIso B S).hom.app ((scalarExtension φ S).obj K) =
      (scalarExtension φ S).map ((rightDerivedLowerStarIdIso A S).hom.app K) := by
  have : PreservesFiniteColimits (lowerStar (ModuleCat.{u + 1} A) (𝟙 S)) :=
    preservesFiniteColimits_of_natIso (lowerStarId (ModuleCat.{u + 1} A) S).symm
  have : PreservesFiniteColimits (lowerStar (ModuleCat.{u + 1} B) (𝟙 S)) :=
    preservesFiniteColimits_of_natIso (lowerStarId (ModuleCat.{u + 1} B) S).symm
  have h := scalarMate_directImage_identity φ S K
  rw [derived_identity_comparison, derived_identity_comparison] at h
  exact h

/-- Scalar compatibility of the normalized identity compactification.
Source: blueprint smooth-purity reduction, Charts.
(blueprint: lem-pur-ordinary-chart-identity-scalar).

Proof: At the sheaf level identify extension by zero and inverse image for the identity by
left-adjoint uniqueness, and derive its actual counit normalization. The open coefficient mate
counit square and the normalized identity pullback comparison then determine the coefficient
square for the derived open-identity isomorphism.
For the proper identity comparison, use the direct-image scalar identity normalization; exactness
of the sheaf identity direct image supplies the required derived comparison normalization.
Expand the identity compactification coefficient arrow as the proper scalar mate followed by
direct image of the open comparison. Naturality moves the open-identity map across the proper
scalar mate; substitute the open and proper identity coefficient squares and cancel the identity
unitors. -/
theorem ordinaryChartIdentityCompactScalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (S : Scheme.{u}) (K : DerivedCategoryModule A S) :
    let eA := Functor.isoWhiskerRight
      (mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) S) _ ≪≫
        Functor.leftUnitor _ ≪≫ rightDerivedLowerStarIdIso A S
    let eB := Functor.isoWhiskerRight
      (mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} B) S) _ ≪≫
        Functor.leftUnitor _ ≪≫ rightDerivedLowerStarIdIso B S
    (compactScalarMap φ (Compactification.ofIsProper (𝟙 S))).app K ≫
        eB.hom.app ((scalarExtension φ S).obj K) =
      (scalarExtension φ S).map (eA.hom.app K) := by
  dsimp only
  have hn := (scalarMate φ (𝟙 S)).naturality
    ((mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) S).hom.app K)
  simp only [Functor.comp_map, Functor.id_obj] at hn
  have ho := congrArg (fun z ↦ (rightDerivedLowerStar (ModuleCat.{u + 1} B)
    (𝟙 S)).map z) (identity_open_scalar φ S K)
  simp only [Functor.map_comp, rightDerivedLowerStar] at ho
  simp only [compactScalarMap, ExceptionalCoefficients.compactSupportMap,
    Compactification.ofIsProper, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app,
    Functor.map_comp, Category.assoc]
  rw [reassoc_of% ho, ← reassoc_of% hn]
  change (scalarExtension φ S).map
      ((rightDerivedLowerStar (ModuleCat.{u + 1} A) (𝟙 S)).map
        ((mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) S).hom.app K)) ≫
        (scalarMate φ (𝟙 S)).app K ≫ 𝟙 _ ≫
          (rightDerivedLowerStarIdIso B S).hom.app ((scalarExtension φ S).obj K) =
    (scalarExtension φ S).map
      ((rightDerivedLowerStar (ModuleCat.{u + 1} A) (𝟙 S)).map
        ((mapDerivedCategoryOpenImmersionLowerShriekId (ModuleCat.{u + 1} A) S).hom.app K)) ≫
          (scalarExtension φ S).map (𝟙 _) ≫
          (scalarExtension φ S).map ((rightDerivedLowerStarIdIso A S).hom.app K)
  simp only [Category.id_comp]
  rw [identity_direct_scalar]
  erw [CategoryTheory.Functor.map_id]
  simp only [Category.id_comp]

end AlgebraicGeometry.Etale
