/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ReductionExtendScalars
public import WeilConjectures.CategoryTheory.Sites.FixedCoefficientDerivedChangeOfRings
public import WeilConjectures.AlgebraicGeometry.SixFunctors.EvaluationHomSiteComparison
public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientOrdinary.FiniteCoefficientOrdinaryDirectImage
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.EtaleProEtaleExceptionalTransport
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalKFlat
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.CoefficientScalarRepresentatives.CoefficientScalarRepresentatives
import all WeilConjectures.CategoryTheory.CoefMonoidalSquareHomTransport
import Mathlib.AlgebraicGeometry.Noetherian
import all WeilConjectures.AlgebraicGeometry.EtaleProEtaleExceptionalTransport
import all WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleExceptionalObjectComparison
import WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarFlatModel
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteDualitySiteComparison
import WeilConjectures.AlgebraicGeometry.Flat.FlatModel
import WeilConjectures.AlgebraicGeometry.SixFunctors.SiteHomComparisonThick
import WeilConjectures.CategoryTheory.Monoidal.Closed.IhomComparison
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ReductionExtendScalars
import WeilConjectures.CategoryTheory.Sites.FixedCoefficientDerivedChangeOfRings
import WeilConjectures.AlgebraicGeometry.SixFunctors.EvaluationHomSiteComparison
import WeilConjectures.AlgebraicGeometry.FiniteCoefficientOrdinary.FiniteCoefficientOrdinaryDirectImage
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible
import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalKFlat
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.CoefficientScalarRepresentatives.CoefficientScalarRepresentatives

/-! # Finite-coefficient internal-Hom site descent

Source: thm-coef-finite-hom.proof.md, final site-comparison sentence
(blueprint: lem-coef-finite-hom-site-descent).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.FiniteHomSiteDescent

private theorem derivedTransport_delta
    {C D : Type (u + 2)}
    [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [F.PreservesKFlatQuasiIso] [F.PreservesFlat]
    [F.IsLeftAdjoint] [F.Monoidal]
    (G : DerivedCategory C ⥤ DerivedCategory D) (e : F.leftDerivedFunctor ≅ G)
    (K M : DerivedCategory C) :
    let := F.leftDerivedFunctorMonoidal
    let := Functor.Monoidal.transport e
    Functor.OplaxMonoidal.δ G K M =
      (e.symm.app (K ⊗ M) ≪≫ (F.leftDerivedTensorIso K).app M ≪≫
        tensorIso (e.app K) (e.app M)).hom := by
  let := F.leftDerivedFunctorMonoidal
  let := Functor.Monoidal.transport e
  dsimp only
  rw [Functor.Monoidal.transport_δ e K M, F.leftDerivedFunctorMonoidal_δ]
  rfl

set_option maxHeartbeats 2000000 in
-- Checking the transported derived tensorator unfolds the K-flat monoidal structure.
private theorem scalarMonoidal_delta
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {A B : Type (u + 1)}
    [CommRing A] [CommRing B] (φ : A →+* B)
    (K M : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A))) :
    let := scalarMonoidal J φ
    Functor.OplaxMonoidal.δ (Sheaf.fixedCoefficientDerivedScalarExtension J φ) K M =
      (scalarTensor J φ K M).hom := by
  unfold scalarMonoidal scalarTensor
  exact derivedTransport_delta (Sheaf.extendScalars J φ)
    (Sheaf.fixedCoefficientDerivedScalarExtension J φ) (scalarResolutionIso J φ) K M

private theorem scalarMonoidal_mu
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {A B : Type (u + 1)}
    [CommRing A] [CommRing B] (φ : A →+* B)
    (K M : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A))) :
    let := scalarMonoidal J φ
    Functor.LaxMonoidal.μ (Sheaf.fixedCoefficientDerivedScalarExtension J φ) K M =
      (scalarTensor J φ K M).inv := by
  let := scalarMonoidal J φ
  apply (cancel_mono (scalarTensor J φ K M).hom).1
  rw [← scalarMonoidal_delta J φ]
  rw [Functor.Monoidal.μ_δ]
  rw [scalarMonoidal_delta J φ]
  exact (scalarTensor J φ K M).inv_hom_id.symm

private theorem scalarHom_eq_comparison
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {A B : Type (u + 1)}
    [CommRing A] [CommRing B] (φ : A →+* B)
    (K M : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A))) :
    let := scalarMonoidal J φ
    scalarHom J φ K M =
      (Functor.LaxMonoidal.ihomComparison
        (Sheaf.fixedCoefficientDerivedScalarExtension J φ) K).natTrans.app M := by
  let := scalarMonoidal J φ
  change scalarHom J φ K M =
    (Functor.LaxMonoidal.ihomComparison
      (Sheaf.fixedCoefficientDerivedScalarExtension J φ) K).natTrans.app M
  rw [Functor.LaxMonoidal.ihomComparison_app_eq_curry, scalarMonoidal_mu]
  rfl

private theorem scalarHom_eq_internalComparison
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {A B : Type (u + 1)}
    [CommRing A] [CommRing B] (φ : A →+* B)
    (K M : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A))) :
    let := scalarMonoidal J φ
    scalarHom J φ K M =
      internalHomComparison (Sheaf.fixedCoefficientDerivedScalarExtension J φ) K M := by
  let := scalarMonoidal J φ
  exact (scalarHom_eq_comparison J φ K M).trans
    (CategoryTheory.comparison_eq (Sheaf.fixedCoefficientDerivedScalarExtension J φ) K M).symm

private theorem scalarEvaluation
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {A B : Type (u + 1)}
    [CommRing A] [CommRing B] (φ : A →+* B)
    (P : ObjectProperty (DerivedCategory (Sheaf J (ModuleCat.{u + 1} A)))) :
    EvaluationLaw J φ P := by
  intro K M _ _
  exact MonoidalClosed.whiskerLeft_curry_ihom_ev_app _ _
    ((scalarTensor J φ K ((ihom K).obj M)).inv ≫
      (Sheaf.fixedCoefficientDerivedScalarExtension J φ).map ((ihom.ev K).app M))

set_option maxHeartbeats 2000000 in
-- The kernel checks the concrete K-flat scalar structure against the generic closed functor.
private theorem scalarTranspose
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {A B : Type (u + 1)}
    [CommRing A] [CommRing B] (φ : A →+* B)
    (P : ObjectProperty (DerivedCategory (Sheaf J (ModuleCat.{u + 1} A)))) :
    TransposeLaw J φ P := by
  let := scalarMonoidal J φ
  intro K M _ _ T f
  have h := CategoryTheory.comparison_transpose
    (Sheaf.fixedCoefficientDerivedScalarExtension J φ) (t := MonoidalClosed.curry f)
  simpa only [← scalarHom_eq_internalComparison, scalarMonoidal_mu,
    MonoidalClosed.uncurry_curry] using h

private theorem scalarComposition
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {A B : Type (u + 1)}
    [CommRing A] [CommRing B] (φ : A →+* B)
    (P : ObjectProperty (DerivedCategory (Sheaf J (ModuleCat.{u + 1} A)))) :
    CompositionLaw J φ P := by
  let := scalarMonoidal J φ
  intro K L M _ _ _
  have h := CategoryTheory.comparison_composition
    (Sheaf.fixedCoefficientDerivedScalarExtension J φ) K L M
  simpa only [← scalarHom_eq_internalComparison, scalarMonoidal_delta] using h

private theorem scalarHom_iso
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {A B : Type (u + 1)}
    [CommRing A] [CommRing B] (φ : A →+* B)
    {K K' M M' : DerivedCategory (Sheaf J (ModuleCat.{u + 1} A))}
    (eK : K ≅ K') (eM : M ≅ M') :
    IsIso (scalarHom J φ K M) ↔ IsIso (scalarHom J φ K' M') := by
  let := scalarMonoidal J φ
  simp only [scalarHom_eq_comparison]
  exact (Functor.LaxMonoidal.isIso_ihomComparison_app_iff_of_iso_left
    (Sheaf.fixedCoefficientDerivedScalarExtension J φ) eK M).trans
      (Functor.LaxMonoidal.isIso_ihomComparison_app_iff_of_iso_right
        (Sheaf.fixedCoefficientDerivedScalarExtension J φ) K' eM)

private theorem etaleCtf_plus (X : Scheme.{u})
    (R : Type (u + 1)) [CommRing R] [Finite R]
    (K : Etale.DerivedCategoryModule R X) (hK : etaleCtf X R K) :
    _root_.DerivedCategory.TStructure.t.plus K := by
  obtain ⟨a, b, _, h⟩ := hK.1.2
  exact ⟨a, (_root_.DerivedCategory.isGE_iff K a).2
    (fun i hi ↦ h i (.inl hi))⟩

private theorem siteDomain (X : Scheme.{u}) [IsNoetherian X]
    (R : Type (u + 1)) [CommRing R] [Finite R] : SiteDomain X R := by
  let N := sitePullback X R
  have hmap : proetaleCtf X R = (etaleCtf X R).map N :=
    ProEtale.exceptionalTransport_object_comparison R X
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro K
    constructor
    · intro hK
      rw [hmap]
      exact ⟨K, hK, ⟨Iso.refl _⟩⟩
    · intro hK
      obtain ⟨a, b, hab, ht⟩ := hK.2.2
      have htK := (ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff
        a b K).1 ht
      have hbounded := _root_.DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn htK
      have hplus : _root_.DerivedCategory.TStructure.t.plus K := ⟨a, hbounded.1⟩
      obtain ⟨L, hL, ⟨e⟩⟩ := (congrFun hmap (N.obj K)).mp hK
      obtain ⟨f, hf⟩ :=
        (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map L K hplus).2 e.hom
      obtain ⟨g, hg⟩ := (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map
        K L (etaleCtf_plus X R L hL)).2 e.inv
      change N.map f = e.hom at hf
      change N.map g = e.inv at hg
      have e' : L ≅ K :=
        ⟨f, g, (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map
          L L (etaleCtf_plus X R L hL)).1 (by
            change N.map (f ≫ g) = N.map (𝟙 L)
            rw [Functor.map_comp, hf, hg, e.hom_inv_id, CategoryTheory.Functor.map_id]),
          (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map
          K K hplus).1 (by
            change N.map (g ≫ f) = N.map (𝟙 K)
            rw [Functor.map_comp, hg, hf, e.inv_hom_id, CategoryTheory.Functor.map_id])⟩
      refine ⟨?_, a, b, hab,
        Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2 htK⟩
      apply (ProEtale.etale_boundedConstructible_iff R X K).2
      exact (Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} R) X
        ).prop_of_iso e' ((ProEtale.etale_boundedConstructible_iff R X L).1 hL.1)
  · intro K L _ hL
    exact ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map K L
      (etaleCtf_plus X R L hL)
  · intro P hP
    exact (congrFun hmap P).mp hP
  · intro K _ a b
    exact Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.trans
      (ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff a b K).symm

private theorem scalarPreservesCtf (X : Scheme.{u}) [IsNoetherian X]
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (K : Etale.DerivedCategoryModule A X) (hK : etaleCtf X A K) :
    etaleCtf X B
      ((Sheaf.fixedCoefficientDerivedScalarExtension X.smallEtaleTopology φ).obj K) := by
  obtain ⟨a, b, hab, ht⟩ := hK.2
  obtain ⟨c, d, _, hv⟩ := hK.1.2
  let L : _root_.DerivedCategory.Bounded
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    ⟨K, ⟨⟨c, (_root_.DerivedCategory.isGE_iff K c).2
      (fun i hi ↦ hv i (.inl hi))⟩,
      ⟨d, (_root_.DerivedCategory.isLE_iff K d).2 (fun i hi ↦ hv i (.inr hi))⟩⟩⟩
  have h := Etale.exists_etaleScalarFlatModel X A B φ a b hab L hK.1.1 ht
  let KB := (Sheaf.fixedCoefficientDerivedScalarExtension X.smallEtaleTopology φ).obj K
  obtain ⟨M, ⟨e⟩⟩ := h.2.2.1
  have e' : M.obj ≅ KB := e
  obtain ⟨c', hc⟩ := M.property.1
  obtain ⟨d', hd⟩ := M.property.2
  have hge : KB.IsGE c' := by
    let := hc
    exact _root_.DerivedCategory.TStructure.t.isGE_of_iso e' c'
  have hle : KB.IsLE d' := by
    let := hd
    exact _root_.DerivedCategory.TStructure.t.isLE_of_iso e' d'
  refine ⟨⟨h.2.2.2.1, min c' d', d', min_le_right _ _, ?_⟩,
    a, b, hab, h.2.2.2.2⟩
  intro i hi
  rcases hi with hi | hi
  · exact (_root_.DerivedCategory.isGE_iff KB c').1 hge i
      (lt_of_lt_of_le hi (min_le_left _ _))
  · exact (_root_.DerivedCategory.isLE_iff KB d').1 hle i hi

section SiteHomComparison
open AlgebraicGeometry.ProEtale
attribute [local irreducible] DerivedCategory.monoidalClosed_of_hasFunctorialFlatResolution

/-- The Noetherian thick-generation argument on the blueprint stratum route.
The generator comparison is the existing proved closed/open adjunction calculation;
no affine-continuity comparison is imported. -/
private theorem siteHomIso (X : Scheme.{u}) [IsNoetherian X]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (K M : Etale.DerivedCategoryModule Λ X)
    (hK : etaleCtf X Λ K) (hM : etaleCtf X Λ M) :
    IsIso (ProEtale.siteComparisonEvaluationHom (ModuleCat.{u + 1} Λ) X K M) := by
  let P := siteHomComparisonLocus Λ X M
  have ht := siteHomComparison_exact_thick Λ X M
  unfold siteHomSiteExactThick siteHomExactThickAssertion at ht
  obtain ⟨sB, sE, β, hβ, _, htri, hret⟩ := ht
  have : P.IsTriangulated := htri
  have : P.IsStableUnderRetracts := hret
  have : P.IsClosedUnderIsomorphisms := by
    refine ⟨fun {B C} e hB ↦ ?_⟩
    change IsIso (siteComparisonEvaluationHom (ModuleCat.{u + 1} Λ) X B M) at hB
    have : IsIso (β.app (op B)) := by simpa only [hβ] using hB
    have : IsIso (β.app (op C)) := NatTrans.isIso_app_of_iso β e.op
    change IsIso (siteComparisonEvaluationHom (ModuleCat.{u + 1} Λ) X C M)
    simpa only [hβ] using (inferInstance : IsIso (β.app (op C)))
  apply etaleThickGeneration X Λ P ?_ K
    hK.1 ?_
  · rintro B ⟨str, i, j, hj, L, hji, hL, hf, ⟨e⟩⟩
    let := hj
    let := hL
    have hs : IsImmersion (str.immersion i) := str.isImmersion i
    let := hs
    have : TopologicalSpace.NoetherianSpace (str.domain i) :=
      (str.immersion i).isEmbedding.isInducing.noetherianSpace
    let c := (str.immersion i).liftCoborder
    let v := (str.immersion i).coborderRange.ι
    have hcv : c ≫ v = str.immersion i := (str.immersion i).liftCoborder_ι
    have : QuasiCompact (c ≫ v) := by rw [hcv]; infer_instance
    have hb := isIso_stratumHom Λ c v L hf
      ⟨M, hM.1⟩
    have hj' : j = (str.immersion i).toImage := by
      apply (cancel_mono (str.immersion i).imageι).mp
      exact hji.trans (Scheme.Hom.toImage_imageι _).symm
    subst j
    obtain ⟨_, he, _⟩ :=
      (etale_locallyClosed_extension_comparison (A := Λ) X (𝟙 X) v).2
        (str.immersion i)
    obtain ⟨es, _, _⟩ := he c v hcv
    have e' : (DerivedCategory.singleFunctor _ 0).obj
        ((Etale.lowerStar (ModuleCat.{u + 1} Λ) (str.immersion i).imageι).obj
          ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ)
            (str.immersion i).toImage).obj L)) ≅
        (locallyClosedEtaleExtension Λ c v).obj
          ((DerivedCategory.singleFunctor _ 0).obj L) := by
      let Q := Etale.lowerStar (ModuleCat.{u + 1} Λ) c ⋙
        Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) v
      have ee : (Etale.lowerStar (ModuleCat.{u + 1} Λ) (str.immersion i).imageι).obj
          ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ)
            (str.immersion i).toImage).obj L) ≅ Q.obj L := by
        exact es.app L
      exact (DerivedCategory.singleFunctor _ 0).mapIso ee ≪≫
        ((Q.mapDerivedCategorySingleFunctor 0).app L).symm ≪≫
        (Functor.mapDerivedCategoryCompIso
          (Etale.lowerStar (ModuleCat.{u + 1} Λ) c)
          (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) v)).app _ ≪≫
        (StratumHomComparisonMate.Etale.extensionIso Λ c v).symm.app _
    exact P.prop_of_iso (e ≪≫ e').symm hb
  · exact hK.2

end SiteHomComparison

private theorem siteHom_eq_generic
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) [(ProEtale.comparisonUpperStar A X).PreservesFlat]
    (K M : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    let := ProEtale.siteComparisonDerivedMonoidal A X
    ProEtale.siteComparisonEvaluationHom A X K M =
      internalHomComparison (ProEtale.comparisonUpperStar A X).mapDerivedCategory K M := by
  let := ProEtale.siteComparisonDerivedMonoidal A X
  unfold ProEtale.siteComparisonEvaluationHom
  exact (CategoryTheory.comparison_eq _ K M).symm

private theorem siteHom_eq (X : Scheme.{u})
    (R : Type (u + 1)) [CommRing R] [Finite R]
    (K M : Etale.DerivedCategoryModule R X) :
    let := ProEtale.siteComparisonDerivedMonoidal (ModuleCat.{u + 1} R) X
    ProEtale.siteComparisonEvaluationHom (ModuleCat.{u + 1} R) X K M =
      internalHomComparison (sitePullback X R) K M := by
  exact siteHom_eq_generic (ModuleCat.{u + 1} R) X K M

private theorem closedSquare
    {C D E H : Type (u + 2)}
    [Category.{u + 1} C] [MonoidalCategory C] [MonoidalClosed C]
    [Category.{u + 1} D] [MonoidalCategory D] [MonoidalClosed D]
    [Category.{u + 1} E] [MonoidalCategory E] [MonoidalClosed E]
    [Category.{u + 1} H] [MonoidalCategory H] [MonoidalClosed H]
    (F : C ⥤ D) (G : E ⥤ H) (U : C ⥤ E) (V : D ⥤ H)
    [F.Monoidal] [G.Monoidal] [U.Monoidal] [V.Monoidal]
    (e : F ⋙ V ≅ U ⋙ G) [NatTrans.IsMonoidal e.hom] (K M : C) :
    e.hom.app ((ihom K).obj M) ≫ G.map (internalHomComparison U K M) ≫
        internalHomComparison G (U.obj K) (U.obj M) =
      V.map (internalHomComparison F K M) ≫
        internalHomComparison V (F.obj K) (F.obj M) ≫
        (MonoidalClosed.internalHom.map (e.inv.app K).op).app (V.obj (F.obj M)) ≫
        (ihom (G.obj (U.obj K))).map (e.hom.app M) := by
  simpa only [CategoryTheory.comparison_comp, internalHomTransport,
    MonoidalClosed.internalHom, Quiver.Hom.unop_op, Functor.comp_obj, Category.assoc]
    using CategoryTheory.comparison_iso e K M

private theorem closedTower
    {C D E : Type (u + 2)}
    [Category.{u + 1} C] [MonoidalCategory C] [MonoidalClosed C]
    [Category.{u + 1} D] [MonoidalCategory D] [MonoidalClosed D]
    [Category.{u + 1} E] [MonoidalCategory E] [MonoidalClosed E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Monoidal] [G.Monoidal] [H.Monoidal]
    (e : F ⋙ G ≅ H) [NatTrans.IsMonoidal e.hom] (K M : C) :
    G.map (internalHomComparison F K M) ≫
        internalHomComparison G (F.obj K) (F.obj M) ≫
        (MonoidalClosed.internalHom.map (e.inv.app K).op).app (G.obj (F.obj M)) ≫
        (ihom (H.obj K)).map (e.hom.app M) =
      e.hom.app ((ihom K).obj M) ≫ internalHomComparison H K M := by
  simpa only [CategoryTheory.comparison_comp, internalHomTransport,
    MonoidalClosed.internalHom, Quiver.Hom.unop_op, Functor.comp_obj, Category.assoc]
    using (CategoryTheory.comparison_iso e K M).symm

private theorem closedSquare_of_eq
    {C D E H : Type (u + 2)}
    [Category.{u + 1} C] [MonoidalCategory C] [MonoidalClosed C]
    [Category.{u + 1} D] [MonoidalCategory D] [MonoidalClosed D]
    [Category.{u + 1} E] [MonoidalCategory E] [MonoidalClosed E]
    [Category.{u + 1} H] [MonoidalCategory H] [MonoidalClosed H]
    (F : C ⥤ D) (G : E ⥤ H) (U : C ⥤ E) (V : D ⥤ H)
    [F.Monoidal] [G.Monoidal] [U.Monoidal] [V.Monoidal]
    (f : ∀ K M, F.obj ((ihom K).obj M) ⟶ (ihom (F.obj K)).obj (F.obj M))
    (g : ∀ K M, G.obj ((ihom K).obj M) ⟶ (ihom (G.obj K)).obj (G.obj M))
    (q : ∀ K M, U.obj ((ihom K).obj M) ⟶ (ihom (U.obj K)).obj (U.obj M))
    (r : ∀ K M, V.obj ((ihom K).obj M) ⟶ (ihom (V.obj K)).obj (V.obj M))
    (hf : ∀ K M, f K M = internalHomComparison F K M)
    (hg : ∀ K M, g K M = internalHomComparison G K M)
    (hq : ∀ K M, q K M = internalHomComparison U K M)
    (hr : ∀ K M, r K M = internalHomComparison V K M)
    (e : F ⋙ V ≅ U ⋙ G) [NatTrans.IsMonoidal e.hom] (K M : C) :
    e.hom.app ((ihom K).obj M) ≫ G.map (q K M) ≫ g (U.obj K) (U.obj M) =
      V.map (f K M) ≫ r (F.obj K) (F.obj M) ≫
        (MonoidalClosed.internalHom.map (e.inv.app K).op).app (V.obj (F.obj M)) ≫
        (ihom (G.obj (U.obj K))).map (e.hom.app M) := by
  rw [hf, hg, hq, hr]
  exact closedSquare F G U V e K M

private theorem closedTower_of_eq
    {C D E : Type (u + 2)}
    [Category.{u + 1} C] [MonoidalCategory C] [MonoidalClosed C]
    [Category.{u + 1} D] [MonoidalCategory D] [MonoidalClosed D]
    [Category.{u + 1} E] [MonoidalCategory E] [MonoidalClosed E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Monoidal] [G.Monoidal] [H.Monoidal]
    (f : ∀ K M, F.obj ((ihom K).obj M) ⟶ (ihom (F.obj K)).obj (F.obj M))
    (g : ∀ K M, G.obj ((ihom K).obj M) ⟶ (ihom (G.obj K)).obj (G.obj M))
    (h : ∀ K M, H.obj ((ihom K).obj M) ⟶ (ihom (H.obj K)).obj (H.obj M))
    (hf : ∀ K M, f K M = internalHomComparison F K M)
    (hg : ∀ K M, g K M = internalHomComparison G K M)
    (hh : ∀ K M, h K M = internalHomComparison H K M)
    (e : F ⋙ G ≅ H) [NatTrans.IsMonoidal e.hom] (K M : C) :
    G.map (f K M) ≫ g (F.obj K) (F.obj M) ≫
        (MonoidalClosed.internalHom.map (e.inv.app K).op).app (G.obj (F.obj M)) ≫
        (ihom (H.obj K)).map (e.hom.app M) =
      e.hom.app ((ihom K).obj M) ≫ h K M := by
  rw [hf, hg, hh]
  exact closedTower F G H e K M

set_option maxHeartbeats 2000000 in
-- The kernel compares the four concrete K-flat monoidal structures with the generic square.
private theorem square_of_monoidal (X : Scheme.{u})
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B)
    (hm : let := scalarMonoidal X.smallEtaleTopology φ
      let := scalarMonoidal (ProEt.topology X) φ
      let := ProEtale.siteComparisonDerivedMonoidal (ModuleCat.{u + 1} A) X
      let := ProEtale.siteComparisonDerivedMonoidal (ModuleCat.{u + 1} B) X
      NatTrans.IsMonoidal (scalarSiteIso X φ).hom)
    (K M : Etale.DerivedCategoryModule A X) : ComparisonSquare X φ K M := by
  let := scalarMonoidal X.smallEtaleTopology φ
  let := scalarMonoidal (ProEt.topology X) φ
  let := ProEtale.siteComparisonDerivedMonoidal (ModuleCat.{u + 1} A) X
  let := ProEtale.siteComparisonDerivedMonoidal (ModuleCat.{u + 1} B) X
  let := hm
  exact closedSquare_of_eq
    (Sheaf.fixedCoefficientDerivedScalarExtension X.smallEtaleTopology φ)
    (Sheaf.fixedCoefficientDerivedScalarExtension (ProEt.topology X) φ)
    (sitePullback X A) (sitePullback X B)
    (scalarHom X.smallEtaleTopology φ) (scalarHom (ProEt.topology X) φ)
    (ProEtale.siteComparisonEvaluationHom (ModuleCat.{u + 1} A) X)
    (ProEtale.siteComparisonEvaluationHom (ModuleCat.{u + 1} B) X)
    (scalarHom_eq_internalComparison X.smallEtaleTopology φ)
    (scalarHom_eq_internalComparison (ProEt.topology X) φ)
    (siteHom_eq X A) (siteHom_eq X B) (scalarSiteIso X φ) K M

set_option maxHeartbeats 2000000 in
-- The kernel compares three transported K-flat structures with the generic scalar tower.
private theorem successive_of_monoidal
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {A B R : Type (u + 1)}
    [CommRing A] [CommRing B] [CommRing R] (φ : A →+* B) (ψ : B →+* R)
    (hm : let := scalarMonoidal J φ
      let := scalarMonoidal J ψ
      let := scalarMonoidal J (ψ.comp φ)
      NatTrans.IsMonoidal (scalarAssoc J φ ψ).hom)
    (P : ObjectProperty (DerivedCategory (Sheaf J (ModuleCat.{u + 1} A)))) :
    SuccessiveLaw J φ ψ P := by
  let := scalarMonoidal J φ
  let := scalarMonoidal J ψ
  let := scalarMonoidal J (ψ.comp φ)
  let := hm
  intro K M _ _
  exact closedTower_of_eq
    (Sheaf.fixedCoefficientDerivedScalarExtension J φ)
    (Sheaf.fixedCoefficientDerivedScalarExtension J ψ)
    (Sheaf.fixedCoefficientDerivedScalarExtension J (ψ.comp φ))
    (scalarHom J φ) (scalarHom J ψ) (scalarHom J (ψ.comp φ))
    (scalarHom_eq_internalComparison J φ) (scalarHom_eq_internalComparison J ψ)
    (scalarHom_eq_internalComparison J (ψ.comp φ)) (scalarAssoc J φ ψ) K M

/-- Transport of the specified finite-coefficient Hom map and its identities from
etale to pro-etale, with intrinsic finite-Tor constructible domains.

Source: thm-coef-finite-hom.proof.md, final two sentences; the expanded five-step
proof of lem-coef-finite-hom-site-descent (blueprint: lem-coef-finite-hom-site-descent).

Proof: finite-ring derived origin supplies bounded constructible etale witnesses.
Tor-interval comparison preserves and reflects the exact interval, testing all
module sheaves on the pro-etale side. Exact site pullback and scalar adjunction
mates give scalarSiteIso and its tensor coherence. The scheme is Noetherian;
the proved stratum comparison and etale thick generation give beta over A.
The scalar flat-model theorem for the arbitrary finite-ring map gives ctf scalar
extensions, and the same thick-generation argument gives beta over B.
Uncurry both paths in ComparisonSquare: naturality for evaluation
and the tensor coherence of scalarSiteIso identify them; the bijective closed
transpose proves equality. All other factors in the square are invertible, so
invertibility on the etale side implies invertibility on its image, hence on every
intrinsic ctf pair by origin. Uncurrying transports evaluation and transpose;
two evaluations give composition. For successive changes use the tensor
coherence of the specified scalar adjunction associator and the closed-comparison
formula for a composite functor. These arguments prove the three individual
laws and the successive law on the ambient derived categories, hence give the
requested transport implications on the intrinsic ctf domains. No independent
invertibility assertion for either scalar-Hom comparison is used. -/
theorem finiteHomSiteDescent
    (k : Type u) [Field k] (p ell : ℕ) [CharP k p]
    (hp : p.Prime) (hk : Finite k ∨ IsAlgClosed k)
    (hell : ell.Prime) (hne : ell ≠ p)
    (X : Scheme.{u}) (aX : X ⟶ Spec (.of k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    (A B : Type (u + 1)) [CommRing A] [CommRing B] [Finite A] [Finite B]
    (hA : ∃ n : ℕ, (ell : A) ^ n = 0) (hB : ∃ n : ℕ, (ell : B) ^ n = 0)
    (φ : A →+* B) :
    SiteDomain X A ∧ SiteDomain X B ∧
    (∀ T, etaleCtf X A T → etaleCtf X B
      ((Sheaf.fixedCoefficientDerivedScalarExtension X.smallEtaleTopology φ).obj T)) ∧
    (∀ K M, etaleCtf X A K → etaleCtf X A M →
      IsIso (ProEtale.siteComparisonEvaluationHom (ModuleCat.{u + 1} A) X K M) ∧
      IsIso (ProEtale.siteComparisonEvaluationHom (ModuleCat.{u + 1} B) X
        ((Sheaf.fixedCoefficientDerivedScalarExtension X.smallEtaleTopology φ).obj K)
        ((Sheaf.fixedCoefficientDerivedScalarExtension X.smallEtaleTopology φ).obj M)) ∧
      ComparisonSquare X φ K M) ∧
    ((∀ K M, etaleCtf X A K → etaleCtf X A M →
        IsIso (scalarHom X.smallEtaleTopology φ K M)) →
      ∀ K M, proetaleCtf X A K → proetaleCtf X A M →
        IsIso (scalarHom (ProEt.topology X) φ K M)) ∧
    (EvaluationLaw X.smallEtaleTopology φ (etaleCtf X A) →
      EvaluationLaw (ProEt.topology X) φ (proetaleCtf X A)) ∧
    (TransposeLaw X.smallEtaleTopology φ (etaleCtf X A) →
      TransposeLaw (ProEt.topology X) φ (proetaleCtf X A)) ∧
    (CompositionLaw X.smallEtaleTopology φ (etaleCtf X A) →
      CompositionLaw (ProEt.topology X) φ (proetaleCtf X A)) ∧
    (∀ (R : Type (u + 1)) [CommRing R] [Finite R],
      (∃ n : ℕ, (ell : R) ^ n = 0) → ∀ ψ : B →+* R,
      SuccessiveLaw X.smallEtaleTopology φ ψ (etaleCtf X A) →
        SuccessiveLaw (ProEt.topology X) φ ψ (proetaleCtf X A)) := by
  -- Retain the blueprint hypotheses in the public statement; the argument is more general.
  have _ := hp
  have _ := hk
  have _ := hell
  have _ := hne
  have _ := hA
  have _ := hB
  clear hp hk hell hne hA hB
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian aX
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  let : IsNoetherian X := ⟨⟩
  have hm : let := scalarMonoidal X.smallEtaleTopology φ
      let := scalarMonoidal (ProEt.topology X) φ
      let := ProEtale.siteComparisonDerivedMonoidal (ModuleCat.{u + 1} A) X
      let := ProEtale.siteComparisonDerivedMonoidal (ModuleCat.{u + 1} B) X
      NatTrans.IsMonoidal (scalarSiteIso X φ).hom := scalarSiteIso_monoidal X φ
  have hassoc (R : Type (u + 1)) [CommRing R] [Finite R] (ψ : B →+* R) :
      let := scalarMonoidal (ProEt.topology X) φ
      let := scalarMonoidal (ProEt.topology X) ψ
      let := scalarMonoidal (ProEt.topology X) (ψ.comp φ)
      NatTrans.IsMonoidal (scalarAssoc (ProEt.topology X) φ ψ).hom :=
    scalarAssoc_monoidal (ProEt.topology X) φ ψ
  have hdA := siteDomain X A
  have hdB := siteDomain X B
  have hs (K M : Etale.DerivedCategoryModule A X) := square_of_monoidal X φ hm K M
  refine ⟨hdA, hdB, scalarPreservesCtf X φ, ?_, ?_,
    fun _ ↦ scalarEvaluation (ProEt.topology X) φ (proetaleCtf X A),
    fun _ ↦ scalarTranspose (ProEt.topology X) φ (proetaleCtf X A),
    fun _ ↦ scalarComposition (ProEt.topology X) φ (proetaleCtf X A), ?_⟩
  · intro K M hK hM
    exact ⟨siteHomIso X A K M hK hM,
      siteHomIso X B _ _ (scalarPreservesCtf X φ K hK)
        (scalarPreservesCtf X φ M hM), hs K M⟩
  · intro hv
    have hi (K M : Etale.DerivedCategoryModule A X)
        (hK : etaleCtf X A K) (hM : etaleCtf X A M) :
        IsIso (scalarHom (ProEt.topology X) φ
          ((sitePullback X A).obj K) ((sitePullback X A).obj M)) := by
      have := siteHomIso X A K M hK hM
      have := siteHomIso X B _ _ (scalarPreservesCtf X φ K hK)
        (scalarPreservesCtf X φ M hM)
      have := hv K M hK hM
      have h := hs K M
      unfold ComparisonSquare at h
      have : IsIso ((scalarSiteIso X φ).hom.app ((ihom K).obj M) ≫
          (Sheaf.fixedCoefficientDerivedScalarExtension (ProEt.topology X) φ).map
            (ProEtale.siteComparisonEvaluationHom (ModuleCat.{u + 1} A) X K M) ≫
          scalarHom (ProEt.topology X) φ
            ((sitePullback X A).obj K) ((sitePullback X A).obj M)) := by
        rw [h]
        infer_instance
      have : IsIso ((Sheaf.fixedCoefficientDerivedScalarExtension (ProEt.topology X) φ).map
          (ProEtale.siteComparisonEvaluationHom (ModuleCat.{u + 1} A) X K M) ≫
          scalarHom (ProEt.topology X) φ
            ((sitePullback X A).obj K) ((sitePullback X A).obj M)) :=
        IsIso.of_isIso_comp_left ((scalarSiteIso X φ).hom.app ((ihom K).obj M)) _
      exact IsIso.of_isIso_comp_left
        ((Sheaf.fixedCoefficientDerivedScalarExtension (ProEt.topology X) φ).map
          (ProEtale.siteComparisonEvaluationHom (ModuleCat.{u + 1} A) X K M))
        (scalarHom (ProEt.topology X) φ ((sitePullback X A).obj K) ((sitePullback X A).obj M))
    intro K M hK hM
    obtain ⟨K', hK', ⟨eK⟩⟩ := hdA.2.2.1 K hK
    obtain ⟨M', hM', ⟨eM⟩⟩ := hdA.2.2.1 M hM
    exact (scalarHom_iso (ProEt.topology X) φ eK eM).mp (hi K' M' hK' hM')
  · intro R _ _ _ ψ _
    exact successive_of_monoidal (ProEt.topology X) φ ψ (hassoc R ψ) (proetaleCtf X A)

end AlgebraicGeometry.FiniteHomSiteDescent
