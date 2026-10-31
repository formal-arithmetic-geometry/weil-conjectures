/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.Sites.FiniteFreeCoefficientExtensionData
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarSheafTensorPullback
import all WeilConjectures.AlgebraicGeometry.Upper.UpperStarTensorCochainRepresentative
import all WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarPullbackTensorKFlat
import all WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarPullbackTensorCoherence
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarPullbackIsoExistence
import all WeilConjectures.AlgebraicGeometry.BoundedFlatCoefficientSiteSquare.BoundedFlatCoefficientSiteSquare
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryMonoidal

/-! # Scalar/site tensor coherence from representative normalization -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.FiniteFreeCoefficients

attribute [local instance] Etale.extensionOplax Etale.extensionAdjMonoidal
  Etale.extensionDeltaIso Etale.extensionEtaIso Etale.extensionMonoidal
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Adjunction.ofIsRightAdjoint Sheaf.adjunction
  ProEtale.pbcFixedScalarExtension
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors Functor.mapDerivedCategoryFactorsh
  ProEtale.pbcComparisonReduction
  DerivedCategory.monoidalClosed DerivedCategory.instMonoidalCategory_weilConjectures
  HasDerivedCategory.standard Etale.scalarRepresentativeTransformation
  Etale.scalarExtensionRepresentative finiteVerdierScalarRepresentative

private theorem ordinary_square
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (X : Scheme.{u})
    (M N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (ProEtale.etaleSheafExtendScalarsCompComparisonUpperStarIso φ X).hom.app (M ⊗ N) ≫
      (ProEtale.sheafExtendScalars φ X).map
        (Functor.OplaxMonoidal.δ (ProEtale.comparisonUpperStar _ X) M N) ≫
      Functor.OplaxMonoidal.δ (ProEtale.sheafExtendScalars φ X) _ _ =
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X).map
        (Functor.OplaxMonoidal.δ (ProEtale.etaleSheafExtendScalars φ X) M N) ≫
      Functor.OplaxMonoidal.δ (ProEtale.comparisonUpperStar _ X) _ _ ≫
      ((ProEtale.etaleSheafExtendScalarsCompComparisonUpperStarIso φ X).hom.app M ⊗ₘ
        (ProEtale.etaleSheafExtendScalarsCompComparisonUpperStarIso φ X).hom.app N) := by
  let : ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) X).comp
      (ProEtale.sheafExtendScalarsAdjunction φ X)).IsMonoidal := by infer_instance
  let : ((ProEtale.etaleSheafExtendScalarsAdjunction φ X).comp
      (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} B) X)).IsMonoidal := by infer_instance
  have : NatTrans.IsMonoidal
      (ProEtale.comparisonLowerStarCompSheafComposeRestrictScalarsIso φ X).hom := by
    exact Functor.isMonoidal_sheafPushforwardContinuousCompSheafComposeIso_hom
      X.toProEt X.smallEtaleTopology (Scheme.ProEt.topology X)
      (A := ModuleCat.{u + 1} B) (ModuleCat.restrictScalars.{u + 1} φ)
  have : NatTrans.IsMonoidal
      (ProEtale.comparisonLowerStarCompSheafComposeRestrictScalarsIso φ X).symm.hom :=
    inferInstanceAs (NatTrans.IsMonoidal
      (ProEtale.comparisonLowerStarCompSheafComposeRestrictScalarsIso φ X).inv)
  have h := conjugateEquiv_symm_app_tensor_comp_δ
    ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) X).comp
      (ProEtale.sheafExtendScalarsAdjunction φ X))
    ((ProEtale.etaleSheafExtendScalarsAdjunction φ X).comp
      (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} B) X))
    (ProEtale.comparisonLowerStarCompSheafComposeRestrictScalarsIso φ X).inv M N
  simpa only [ProEtale.etaleSheafExtendScalarsCompComparisonUpperStarIso,
    conjugateIsoEquiv_symm_apply_hom, Iso.symm_hom,
    Functor.OplaxMonoidal.comp_δ, Functor.comp_obj, Category.assoc] using h


private theorem exact_representative_quotient
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (P : CochainComplex C ℤ) :
    F.mapDerivedCategoryFactors.hom.app P =
      F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) := by
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  change _ = F.mapDerivedCategory.map (𝟙 _) ≫ _ ≫ 𝟙 _ ≫ DerivedCategory.Qh.map (𝟙 _)
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  simp only [Category.id_comp, Category.comp_id]
  exact (Category.comp_id _).symm

section ExactNormalization
universe v w w'
variable {C : Type w} {D : Type w'} [Category.{v + 1} C] [Category.{v + 1} D]
  [Abelian C] [Abelian D]
  [IsGrothendieckAbelian.{v + 1} C] [IsGrothendieckAbelian.{v + 1} D]
  [MonoidalCategory C] [MonoidalCategory D]
  [MonoidalPreadditive C] [MonoidalPreadditive D]
  [MonoidalClosed C] [MonoidalClosed D] [BraidedCategory C] [BraidedCategory D]
  [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]

private theorem exact_site_normalization :
    Etale.LaxSquareHδ (Q₁ := DerivedCategory.Q) (Q₂ := DerivedCategory.Q)
      (F := F.mapHomologicalComplex (.up ℤ)) F.mapDerivedCategoryTensorComparison
      (fun P ↦ F.mapDerivedCategoryFactors.hom.app P) := by
  exact Etale.cochain_tensor_counit_core F F.mapDerivedCategory
    F.mapDerivedCategoryTensorComparison F.mapDerivedCategoryFactorsh.hom _
    (exact_representative_quotient F) F.mapDerivedCategoryTensorComparison_app_app_comp
end ExactNormalization

private def genericSiteTensorComparison
    (C : Type (u + 2)) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C]
    [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C]
    (X : Scheme.{u}) [(ProEtale.comparisonUpperStar C X).PreservesFlat] :=
  (ProEtale.comparisonUpperStar C X).mapDerivedCategoryTensorComparison

private theorem generic_site_tensor_normalization
    (C : Type (u + 2)) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C]
    [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C]
    (X : Scheme.{u}) [(ProEtale.comparisonUpperStar C X).PreservesFlat] :
    let F := ProEtale.comparisonUpperStar C X
    Etale.LaxSquareHδ (Q₁ := DerivedCategory.Q) (Q₂ := DerivedCategory.Q)
      (F := F.mapHomologicalComplex (.up ℤ)) (genericSiteTensorComparison C X)
      (fun P ↦ F.mapDerivedCategoryFactors.hom.app P) := by
  exact exact_site_normalization (ProEtale.comparisonUpperStar C X)

private theorem native_representative_square
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (X : Scheme.{u})
    (K : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    (Sites.scalarSite φ X).inv.app (DerivedCategory.Q.obj K) ≫
      (Sites.scalar true φ X).map
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A)
          X).mapDerivedCategoryFactors.hom.app K) ≫
      finiteVerdierScalarRepresentative (Scheme.ProEt.topology X) φ
        (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A)
          X).mapHomologicalComplex (.up ℤ)).obj K) =
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory.map
        (Etale.scalarExtensionRepresentative φ X K) ≫
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategoryFactors.hom.app
        (((ProEtale.etaleSheafExtendScalars φ X).mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (ProEtale.etaleSheafExtendScalarsCompComparisonUpperStarIso φ X).hom (.up ℤ)).app K) := by
  with_unfolding_all
    exact (ProEtale.BoundedFlatCoefficientSiteSquare.comparison_normalization X φ K).symm

private theorem representative_app
    {C : Type*} {D : Type*} [Category.{u + 1} C] [Category.{u + 1} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{u + 1} C]
    [HasDerivedCategory.{u + 1} D]
    (E : C ⥤ D) (U : D ⥤ C) [E.Additive] [U.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (a : E ⊣ U) {L : DerivedCategory C ⥤ DerivedCategory D}
    (d : L ⊣ U.mapDerivedCategory) (P : CochainComplex C ℤ) :
    (ProEtale.BoundedFlatCoefficientSiteSquare.representative E U a d).app P =
      finiteVerdierScalarRepresentativeAux E U a d P := rfl

private def genericScalarRepresentative
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) :
    DerivedCategory.Q ⋙ ProEtale.pbcFixedScalarExtension J φ ⟶
      (finiteVerdierOrdinaryExtension J φ).mapHomologicalComplex
        (.up ℤ) ⋙ DerivedCategory.Q := by
  unfold ProEtale.pbcFixedScalarExtension
  simpa only [Sheaf.derivedRestrictScalars] using
    ProEtale.BoundedFlatCoefficientSiteSquare.representative
      (finiteVerdierOrdinaryExtension J φ)
      (Sheaf.restrictScalars J φ)
      (finiteVerdierOrdinaryAdjunction J φ)
      (Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars J φ))

private theorem genericScalarRepresentative_app
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B)
    (P : CochainComplex (Sheaf J (ModuleCat.{u + 1} A)) ℤ) :
    (genericScalarRepresentative J φ).app P =
      finiteVerdierScalarRepresentative J φ P := by
  unfold genericScalarRepresentative finiteVerdierScalarRepresentative
  dsimp only [_root_.id]
  unfold ProEtale.pbcFixedScalarExtension
  simpa only [Sheaf.derivedRestrictScalars] using representative_app
    (finiteVerdierOrdinaryExtension J φ)
    (Sheaf.restrictScalars J φ)
    (finiteVerdierOrdinaryAdjunction J φ)
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars J φ)) P

private def siteScalarRepresentative
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) :
    DerivedCategory.Q ⋙ ProEtale.pbcFixedScalarExtension (Scheme.ProEt.topology X) φ ⟶
      (finiteVerdierOrdinaryExtension (Scheme.ProEt.topology X) φ).mapHomologicalComplex
        (.up ℤ) ⋙ DerivedCategory.Q :=
  genericScalarRepresentative (Scheme.ProEt.topology X) φ

private theorem siteScalarRepresentative_app
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u})
    (P : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) ℤ) :
    (siteScalarRepresentative φ X).app P =
      finiteVerdierScalarRepresentative (Scheme.ProEt.topology X) φ P :=
  genericScalarRepresentative_app (Scheme.ProEt.topology X) φ P

private def nativeScalarTensorComparison
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) (μ : Sites.TensorComparison true φ X) :
    Functor.uncurry.obj (curriedTensor
      (DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))) ⋙
        ProEtale.pbcFixedScalarExtension (Scheme.ProEt.topology X) φ ≅
    (ProEtale.pbcFixedScalarExtension (Scheme.ProEt.topology X) φ).prod
        (ProEtale.pbcFixedScalarExtension (Scheme.ProEt.topology X) φ) ⋙
      Functor.uncurry.obj (curriedTensor
        (DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)))) := by
  exact μ

private theorem nativeScalarTensorComparison_normalized
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) (μ : Sites.TensorComparison true φ X)
    (hμ : Sites.NormalizedTensor true φ X μ) :
    letI := (finiteVerdierOrdinaryAdjunction (Scheme.ProEt.topology X) φ).isLeftAdjoint
    Etale.ExceptionalCoefficients.TensorNormalizationAux
      (finiteVerdierOrdinaryExtension (Scheme.ProEt.topology X) φ)
      (ProEtale.pbcFixedScalarExtension (Scheme.ProEt.topology X) φ)
      (finiteVerdierScalarRepresentative (Scheme.ProEt.topology X) φ)
      (nativeScalarTensorComparison φ X μ) := by
  obtain ⟨δ, hδ, heq⟩ := hμ
  have he : nativeScalarTensorComparison φ X μ = δ := eq_of_heq heq
  exact he.symm ▸ hδ


set_option maxHeartbeats 1000000 in
-- Budget for comparing the four derived normalization maps.
private theorem normalized_site_tensor_kflat
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (X : Scheme.{u})
    (μ : Sites.TensorComparison true φ X) (hμ : Sites.NormalizedTensor true φ X μ)
    (P R : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P)
    (hR : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat R) :
    (Sites.scalarSite φ X).inv.app (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj R) ≫
      (Sites.scalar true φ X).map
        (((genericSiteTensorComparison (ModuleCat.{u + 1} A) X).app
            (DerivedCategory.Q.obj P)).app
            (DerivedCategory.Q.obj R)) ≫
      μ.hom.app ((Sites.nu A X).obj (DerivedCategory.Q.obj P),
        (Sites.nu A X).obj (DerivedCategory.Q.obj R)) =
    (Sites.nu B X).map ((Etale.ExceptionalCoefficients.tensorIso φ X).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj R)) ≫
      (((genericSiteTensorComparison (ModuleCat.{u + 1} B) X).app
          ((Sites.scalar false φ X).obj (DerivedCategory.Q.obj P))).app
            ((Sites.scalar false φ X).obj (DerivedCategory.Q.obj R))) ≫
      ((Sites.scalarSite φ X).inv.app (DerivedCategory.Q.obj P) ⊗ₘ
        (Sites.scalarSite φ X).inv.app (DerivedCategory.Q.obj R)) := by
  let EY := ProEtale.etaleSheafExtendScalars φ X
  let FB := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} B) X
  let FA := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X
  let EX := finiteVerdierOrdinaryExtension (Scheme.ProEt.topology X) φ
  let : EX.IsLeftAdjoint :=
    (finiteVerdierOrdinaryAdjunction (Scheme.ProEt.topology X) φ).isLeftAdjoint
  let : ∀ M N, IsIso (Functor.OplaxMonoidal.δ EX M N) := fun M N ↦
    isIso_δ_composeAndSheafify (Scheme.ProEt.topology X)
      (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ) M N
  let SY := Etale.scalarExtension φ X
  let SX := ProEtale.pbcFixedScalarExtension (Scheme.ProEt.topology X) φ
  let rX := siteScalarRepresentative φ X
  have hδ := nativeScalarTensorComparison_normalized φ X μ hμ
  apply normalized_cochain_square EY FB FA EX SY FB.mapDerivedCategory
    FA.mapDerivedCategory SX (Etale.scalarRepresentativeTransformation φ X)
    FB.mapDerivedCategoryFactors.hom FA.mapDerivedCategoryFactors.hom rX
    (Etale.scalarExtensionRepresentative φ X)
    (fun K ↦ FB.mapDerivedCategoryFactors.hom.app K)
    (fun K ↦ FA.mapDerivedCategoryFactors.hom.app K)
    (finiteVerdierScalarRepresentative (Scheme.ProEt.topology X) φ)
    (Etale.scalar_rep_app φ X) (fun _ ↦ rfl) (fun _ ↦ rfl)
    (siteScalarRepresentative_app φ X)
    (Etale.ExceptionalCoefficients.tensorIso φ X)
    (genericSiteTensorComparison (ModuleCat.{u + 1} B) X)
    (genericSiteTensorComparison (ModuleCat.{u + 1} A) X)
    (nativeScalarTensorComparison φ X μ)
    (Etale.scalar_tensor_normalization φ X)
    (generic_site_tensor_normalization (ModuleCat.{u + 1} B) X)
    (generic_site_tensor_normalization (ModuleCat.{u + 1} A) X) hδ
    (Sites.scalarSite φ X).symm
    (ProEtale.etaleSheafExtendScalarsCompComparisonUpperStarIso φ X)
    (Functor.mapHomologicalComplexCompIso
      (ProEtale.etaleSheafExtendScalarsCompComparisonUpperStarIso φ X) (.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (FA ⋙ EX)) (.up ℤ)).symm)
    rfl (ordinary_square φ X)
    (by
      intro K _
      simp only [Functor.mapHomologicalComplexCompIso, NatIso.mapHomologicalComplex,
        Iso.symm_hom, Iso.refl_inv, NatTrans.mapHomologicalComplex_id]
      with_unfolding_all
        exact native_representative_square φ X K)
    (Etale.scalarRepresentativeTransformation_isIso φ X) (fun _ ↦ inferInstance) P R hP hR


private def uncurryTensorIso
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    (TC : C ⥤ C ⥤ C) (TD : D ⥤ D ⥤ D)
    (δ : (Functor.postcompose₂.obj F).obj TC ⟶
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj TD) [IsIso δ] :
    Functor.uncurry.obj TC ⋙ F ≅ F.prod F ⋙ Functor.uncurry.obj TD := by
  let t := Etale.uncurryTensorComparison F TC TD δ
  exact NatIso.ofComponents (fun KL ↦ ((asIso δ).app KL.1).app KL.2)
    (fun f ↦ t.naturality f)

private theorem uncurryTensorIso_hom_app
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    (TC : C ⥤ C ⥤ C) (TD : D ⥤ D ⥤ D)
    (δ : (Functor.postcompose₂.obj F).obj TC ⟶
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj TD) [IsIso δ] (K M : C) :
    (uncurryTensorIso F TC TD δ).hom.app (K, M) = (δ.app K).app M := rfl

private theorem canonical_site_tensor_agreement
    (C : Type (u + 2)) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C]
    [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C]
    (X : Scheme.{u}) [(ProEtale.comparisonUpperStar C X).PreservesFlat]
    (K M : DerivedCategory (Sheaf X.smallEtaleTopology C)) :
    (((ProEtale.comparisonUpperStar C X).mapDerivedCategoryTensorComparison).app K).app M =
      (ProEtale.siteComparisonTensorIso C X K).hom.app M := by
  rw [ProEtale.siteComparisonTensorIso_hom_app]
  have h := ProEtale.siteComparisonDerivedMonoidal_δ C X K M
  with_unfolding_all
    exact (Functor.mapDerivedCategoryTensorComparison_app_app
      (ProEtale.comparisonUpperStar C X) K M).trans h.symm

private def nativeSiteTensor
    (C : Type (u + 2)) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C]
    [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C]
    (X : Scheme.{u}) [(ProEtale.comparisonUpperStar C X).PreservesFlat]
    : Functor.uncurry.obj (Etale.derivedTensor C X) ⋙
        (ProEtale.comparisonUpperStar C X).mapDerivedCategory ≅
      (ProEtale.comparisonUpperStar C X).mapDerivedCategory.prod
          (ProEtale.comparisonUpperStar C X).mapDerivedCategory ⋙
        Functor.uncurry.obj (ProEtale.derivedTensor C X) :=
  uncurryTensorIso (ProEtale.comparisonUpperStar C X).mapDerivedCategory
    (curriedTensor _) (curriedTensor _)
    (ProEtale.comparisonUpperStar C X).mapDerivedCategoryTensorComparison

private theorem nativeSiteTensor_hom_app_exact
    (C : Type (u + 2)) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C]
    [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C]
    (X : Scheme.{u}) [(ProEtale.comparisonUpperStar C X).PreservesFlat]
    (K M : DerivedCategory (Sheaf X.smallEtaleTopology C)) :
    (nativeSiteTensor C X).hom.app (K, M) =
      (((ProEtale.comparisonUpperStar C X).mapDerivedCategoryTensorComparison).app K).app M :=
  uncurryTensorIso_hom_app (ProEtale.comparisonUpperStar C X).mapDerivedCategory
    (curriedTensor _) (curriedTensor _)
    (ProEtale.comparisonUpperStar C X).mapDerivedCategoryTensorComparison K M

private theorem nativeSiteTensor_hom_app
    (C : Type (u + 2)) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C]
    [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C]
    (X : Scheme.{u}) [(ProEtale.comparisonUpperStar C X).PreservesFlat]
    (K M : DerivedCategory (Sheaf X.smallEtaleTopology C)) :
    (nativeSiteTensor C X).hom.app (K, M) =
      (ProEtale.siteComparisonTensorIso C X K).hom.app M :=
  (nativeSiteTensor_hom_app_exact C X K M).trans (canonical_site_tensor_agreement C X K M)

private theorem nativeSiteTensor_inv_app
    (C : Type (u + 2)) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C]
    [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C]
    (X : Scheme.{u}) [(ProEtale.comparisonUpperStar C X).PreservesFlat]
    (K M : DerivedCategory (Sheaf X.smallEtaleTopology C)) :
    (nativeSiteTensor C X).inv.app (K, M) =
      (ProEtale.siteComparisonTensorIso C X K).inv.app M := by
  with_unfolding_all
    exact congrArg (fun i ↦ i.inv) (Iso.ext (nativeSiteTensor_hom_app C X K M))

private def siteTensor (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u}) :
    Functor.uncurry.obj (Sites.tensor false A X) ⋙ Sites.nu A X ≅
      (Sites.nu A X).prod (Sites.nu A X) ⋙ Functor.uncurry.obj (Sites.tensor true A X) := by
  dsimp only [Sites.tensor, Sites.nu, Etale.derivedTensor, ProEtale.derivedTensor, _root_.id]
  exact nativeSiteTensor (ModuleCat.{u + 1} A) X

private theorem siteTensor_hom_app
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u}) (K M : Cat A X) :
    (siteTensor A X).hom.app (K, M) =
      (ProEtale.siteComparisonTensorIso (ModuleCat.{u + 1} A) X K).hom.app M := by
  with_unfolding_all
    exact nativeSiteTensor_hom_app (ModuleCat.{u + 1} A) X K M


private def rawSiteTensor (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u}) :
    Functor.uncurry.obj (curriedTensor (Cat A X)) ⋙ Sites.nu A X ≅
      (Sites.nu A X).prod (Sites.nu A X) ⋙
        Functor.uncurry.obj (curriedTensor (Sites.D true A X)) := by
  with_unfolding_all exact nativeSiteTensor (ModuleCat.{u + 1} A) X

private theorem rawSiteTensor_hom_app
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u}) (K M : Cat A X) :
    (rawSiteTensor A X).hom.app (K, M) =
      (ProEtale.siteComparisonTensorIso (ModuleCat.{u + 1} A) X K).hom.app M := by
  with_unfolding_all exact nativeSiteTensor_hom_app (ModuleCat.{u + 1} A) X K M

private theorem rawSiteTensor_generic_app
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u}) (K M : Cat A X) :
    (rawSiteTensor A X).hom.app (K, M) =
      ((genericSiteTensorComparison (ModuleCat.{u + 1} A) X).app K).app M := by
  with_unfolding_all
    exact nativeSiteTensor_hom_app_exact (ModuleCat.{u + 1} A) X K M

/-- The normalized scalar/site comparison respects the canonical binary tensor maps.
Source: Stacks 07A4, 03EL, 0G7E and the blueprint finite-free extension proof.
(blueprint: lem-sf-normalized-stage-site-tensor-square).
Proof: the ordinary comparison is the monoidal conjugate of the sectionwise
restriction identity. The cochain representative comparison is the established
scalar/site mate normalization. The four normalization equations therefore give
the tensor square on K-flat representatives by cancellation of their scalar
and exact-site representative isomorphisms. Naturality and flat K-flat resolutions
in each variable give the equation for arbitrary derived objects. -/
theorem normalized_site_tensor_square
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (X : Scheme.{u})
    (μ : Sites.TensorComparison true φ X) (hμ : Sites.NormalizedTensor true φ X μ)
    (K M : Cat A X) :
    (Sites.scalarSite φ X).inv.app (K ⊗ M) ≫
      (Sites.scalar true φ X).map
        ((ProEtale.siteComparisonTensorIso (ModuleCat.{u + 1} A) X K).hom.app M) ≫
      μ.hom.app ((Sites.nu A X).obj K, (Sites.nu A X).obj M) =
    (Sites.nu B X).map ((Etale.ExceptionalCoefficients.tensorIso φ X).hom.app (K, M)) ≫
      (ProEtale.siteComparisonTensorIso (ModuleCat.{u + 1} B) X
        ((Sites.scalar false φ X).obj K)).hom.app ((Sites.scalar false φ X).obj M) ≫
      ((Sites.scalarSite φ X).inv.app K ⊗ₘ (Sites.scalarSite φ X).inv.app M) := by
  with_unfolding_all
    let F := Sites.scalar false φ X
    let G := Sites.scalar true φ X
    let P := Sites.nu A X
    let Q := Sites.nu B X
    let TY := Functor.uncurry.obj (curriedTensor (Cat A X))
    let TX := Functor.uncurry.obj (curriedTensor (Sites.D true B X))
    let tF : TY ⋙ F ≅ F.prod F ⋙ Functor.uncurry.obj (curriedTensor (Cat B X)) := by
      with_unfolding_all
        exact Etale.ExceptionalCoefficients.tensorIso φ X
    let tG : Functor.uncurry.obj (curriedTensor (Sites.D true A X)) ⋙ G ≅
        G.prod G ⋙ TX := by
      with_unfolding_all exact μ
    let tP := (rawSiteTensor A X).hom
    let tQ := (rawSiteTensor B X).hom
    let a := (Sites.scalarSite φ X).symm
    let α : TY ⋙ F ⋙ Q ⟶ P.prod P ⋙ G.prod G ⋙ TX :=
      Functor.whiskerLeft TY a.hom ≫ Functor.whiskerRight tP G ≫
        Functor.whiskerLeft (P.prod P) tG.hom
    let β : TY ⋙ F ⋙ Q ⟶ P.prod P ⋙ G.prod G ⋙ TX :=
      Functor.whiskerRight tF.hom Q ≫ Functor.whiskerLeft (F.prod F) tQ ≫
        Functor.whiskerRight (NatTrans.prod a.hom a.hom) TX
    have h : α = β := by
      apply Etale.natTrans_ext_flat α β
      intro U V hU hV _ _
      dsimp only [α, β, TY, TX, P, Q, F, G, tF, tP, tQ, a, Iso.symm_hom,
        Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
        Functor.uncurry_obj_obj, Functor.prod_obj, Functor.comp_obj, NatTrans.prod]
      dsimp only [tG]
      rw [rawSiteTensor_generic_app, rawSiteTensor_generic_app]
      have hk := normalized_site_tensor_kflat φ X μ hμ U V hU hV
      simp only [Sites.tensor, _root_.id, Etale.derivedTensor, ProEtale.derivedTensor,
        curriedTensor_obj_obj, Etale.uncurryCurriedTensor_map,
        Functor.comp_obj, Functor.prod_obj, Functor.uncurry_obj_obj] at hk ⊢
      with_unfolding_all
        convert! hk using 1
    have h' := congrArg (fun t ↦ t.app (K, M)) h
    dsimp only [α, β, TY, TX, P, Q, F, G, tF, tP, tQ, a, Iso.symm_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
      Functor.uncurry_obj_obj, Functor.prod_obj, Functor.comp_obj, NatTrans.prod,
      Etale.uncurryTensorComparison] at h'
    rw [rawSiteTensor_hom_app, rawSiteTensor_hom_app] at h'
    dsimp only [tG] at h'
    simp only [Sites.tensor, _root_.id, Etale.derivedTensor, ProEtale.derivedTensor,
      curriedTensor_obj_obj, Etale.uncurryCurriedTensor_map,
      Functor.comp_obj, Functor.prod_obj, Functor.uncurry_obj_obj] at h' ⊢
    with_unfolding_all
      convert! h' using 1
end WeilConjectures.FiniteFreeCoefficients
