/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Sheaf.Paper.ProEtaleConstructibleSheaf
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
public import Sheaf.SecSmoothPurity.ScalarExtensionFunctor
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Sheaf.SecSmoothPurity.ReductionDirectImage
public import Sheaf.Paper.ComparisonPullbackExact
public import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
public import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Sheaf.Paper.EtaleProEtaleAdjunctionTransfer
public import Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization
public import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FiniteEtale
public import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
public import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
public import Sheaf.Paper.WitnessCompatibility
public import Sheaf.Paper.PurEtaleScalarMateProjection
public import Sheaf.Paper.ProperOpenCoefficientRefinement
import Sheaf.Paper.EtaleProEtaleCompactScalarSquare
import Sheaf.Paper.FiniteCompactSupportDomains
import Sheaf.Paper.EtaleSumScalarRepresentative
import Sheaf.AlgebraicGeometry.EtaleFlatConstructibleModel
import all Sheaf.AlgebraicGeometry.EtaleCompactificationBoundedModels
import all Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
import Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphSheafNormalization
public import Sheaf.Paper.EtaleProEtaleCoefficientTransport

/-! # Etale/pro-etale coefficient compatibility

Source: Stacks Project, Tags 0GL6 and 0F7J; the Charts and Locality paragraphs of
main-20261015 `det-sp-reduction-exceptional`
(blueprint: lem-sp-et-proet-coefficient-compatibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u v
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
private theorem cachedEtaleGroth (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  inferInstance
private theorem cachedEtaleSheafify (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : HasSheafify X.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  inferInstance
private theorem cachedEtaleMonoidalPreadditive (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : MonoidalPreadditive (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} A)) := inferInstance
private theorem cachedEtaleCoproducts (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : HasCountableCoproducts (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} A)) := inferInstance
private theorem cachedEtaleColimits (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : HasColimitsOfShape ℤ (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} A)) := inferInstance
private theorem cachedEtaleFlatResolution (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : Abelian.HasFunctorialFlatResolution (Sheaf
      X.smallEtaleTopology (ModuleCat.{u + 1} A)) := inferInstance
private theorem cachedEtaleInjectiveResolution (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : Abelian.HasKInjectiveResolutions (Sheaf
      X.smallEtaleTopology (ModuleCat.{u + 1} A)) := inferInstance
private theorem cachedEtaleExactColimits (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : HasExactColimitsOfShape ℤ (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} A)) := inferInstance
private theorem cachedEtaleTensor4 (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : ∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} A))),
    GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := inferInstance
private theorem cachedEtaleTensor12 (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : ∀ (X₁ X₂ X₃ : GradedObject ℤ (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} A))),
    GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := inferInstance
private theorem cachedEtaleTensor23 (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : ∀ (X₁ X₂ X₃ : GradedObject ℤ (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} A))),
    GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := inferInstance
private theorem cachedEtaleTensorColimits (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : ∀ (V : (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))),
    PreservesColimitsOfShape ℤ ((CategoryTheory.MonoidalCategory.curriedTensor (Sheaf
      X.smallEtaleTopology (ModuleCat.{u + 1} A))).obj V) :=
  inferInstance
private theorem cachedEtaleTensorFlipColimits (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : ∀ (V : (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))),
    PreservesColimitsOfShape ℤ ((CategoryTheory.MonoidalCategory.curriedTensor (Sheaf
      X.smallEtaleTopology (ModuleCat.{u + 1} A))).flip.obj V) :=
  inferInstance


namespace AlgebraicGeometry.Etale
attribute [local instance 2000] cachedEtaleGroth cachedEtaleSheafify
  cachedEtaleMonoidalPreadditive cachedEtaleCoproducts
  cachedEtaleColimits cachedEtaleFlatResolution
  cachedEtaleInjectiveResolution cachedEtaleExactColimits
  cachedEtaleTensor4 cachedEtaleTensor12 cachedEtaleTensor23
  cachedEtaleTensorColimits cachedEtaleTensorFlipColimits
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Functor.leftDerivedFunctor upperStar lowerStar openImmersionLowerShriek
  ProEtale.pbcFixedScalarExtension

private theorem acyclic_eq_unit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] (P : CochainComplex C ℤ) :
    DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (.up ℤ)).inv.app P) ≫
        F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) =
      F.rightDerivedFunctorUnitQ P := by
  unfold Functor.rightDerivedFunctorUnitQ
  change DerivedCategory.Qh.map (𝟙 _) ≫ _ = 𝟙 _ ≫ _ ≫ F.rightDerivedFunctor.map (𝟙 _)
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]


attribute [local irreducible] DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  Functor.mapDerivedCategoryFactors
  Functor.rightDerivedFunctorUnitQ properAcyclicComparison
  etaleSumCompactifiedModelBoundary etaleSumCompactifiedComplexMap

private theorem normalization_graph
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (N : EtaleCompactSupportNormalization A)
    (e : X ⟶ Y) [Etale e] [IsSeparated e] (c : Compactification e) :
    N.sheafComparison e c = etaleCompactificationGraphMap A e c := by
  apply NatTrans.ext
  funext M
  let := compactification_comparison_mono A c M
  apply (cancel_mono ((compactificationSheafToDirectImage A c).app M)).mp
  exact (N.sheaf_normalization e c M).trans
    (compactSupportGraphSheafComparison_normalization A e c M).symm

private theorem normalization_boundary
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (N : EtaleCompactSupportNormalization A)
    (e : X ⟶ Y) [Etale e] [IsSeparated e] [QuasiCompact e]
    (c : Compactification e)
    (P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (a b : ℤ) (hz : ∀ q : ℤ, q < a ∨ b < q → IsZero (P.X q)) :
    (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategoryFactors.hom.app
        P ≫ etaleSumCompactifiedModelBoundary A e c P =
      (N.comparison e c).inv.app (DerivedCategory.Q.obj P) := by
  obtain ⟨_, ν, hν, hmodel⟩ := etaleCompactification_bounded_models A N e c
  have he := (hmodel P a b hz).2.2.1
  have hg : ν.inv = etaleCompactificationGraphMap A e c :=
    hν.trans (normalization_graph A N e c)
  apply (cancel_mono ((N.comparison e c).hom.app (DerivedCategory.Q.obj P) ≫
    (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategoryFactors.hom.app
      P)).mp
  simp only [Category.assoc]
  unfold etaleSumCompactifiedModelBoundary
  have hu : properAcyclicComparison A c.g (compactifiedEtaleOpenComplex A c P) ≫
      (rightDerivedLowerStar (ModuleCat.{u + 1} A) c.g).map
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategoryFactors.inv.app
          P) = etaleCompactificationAcyclicComparison A c P := by
    unfold properAcyclicComparison etaleCompactificationAcyclicComparison
    erw [acyclic_eq_unit]
    rfl
  simp only [Category.assoc]
  erw [reassoc_of% hu, he]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [etaleSumCompactifiedComplexMap, ← hg]
  rw [← DerivedCategory.Q.map_comp]
  have hi := (NatIso.mapHomologicalComplex ν (.up ℤ)).inv_hom_id_app P
  change (NatTrans.mapHomologicalComplex ν.inv (.up ℤ)).app P ≫
    (NatIso.mapHomologicalComplex ν (.up ℤ)).hom.app P = 𝟙 _ at hi
  rw [hi, CategoryTheory.Functor.map_id]
  exact Category.comp_id _
end AlgebraicGeometry.Etale
namespace AlgebraicGeometry.ProEtale.CoefficientCompatibility

attribute [local instance 2000] cachedEtaleGroth cachedEtaleSheafify
  cachedEtaleMonoidalPreadditive cachedEtaleCoproducts cachedEtaleColimits
  cachedEtaleFlatResolution cachedEtaleInjectiveResolution cachedEtaleExactColimits
  cachedEtaleTensor4 cachedEtaleTensor12 cachedEtaleTensor23
  cachedEtaleTensorColimits cachedEtaleTensorFlipColimits

attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Functor.leftDerivedFunctor
  Etale.upperStar Etale.lowerStar Etale.openImmersionLowerShriek
  ProEtale.upperStar ProEtale.lowerStar ProEtale.openImmersionLowerShriek


/-- The etale coefficient map is the proper counit mate followed by the canonical
open tensor identification. Source: Stacks 0GL6 and blueprint Charts paragraph
(blueprint: lem-sp-et-proet-coefficient-compatibility). -/
def etaleCoefficientMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : Etale.DerivedCategoryModule A X) :
    (Etale.scalarExtension φ Y).obj
        ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj K) ⟶
      (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).obj
        ((Etale.scalarExtension φ X).obj K) :=
  (Etale.scalarMate φ c.g).app
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj K) ≫
    (Etale.rightDerivedLowerStar (ModuleCat.{u + 1} B) c.g).map
      (Etale.properOpenCoefficientOpenIso φ c.i K).hom

/-- The pro-etale coefficient arrow is the genuine fixed-module transport of the
recorded intrinsic reductionDirectImageComparison, using its normalized realization,
scalar and compact-support presentation comparisons.
Source: Stacks 0GL6 and blueprint Charts paragraph
(blueprint: lem-sp-et-proet-coefficient-compatibility). -/
def proEtaleCoefficientMap
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c ⋙ liftedScalarExtension φ Y ⟶
      liftedScalarExtension φ X ⋙ rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) c :=
  transportedRecordedReductionDirectImageComparison φ c
    (reductionDirectImageComparison φ c.i c.g)

/-- Summandwise coefficient extension for the exact etale sum functor. It is the
left-adjoint comparison whose right-adjoint comparison is restriction of scalars
commuting with inverse image. On K-flat representatives it preserves each sheet summand.
Source: Stacks 03S6 and 0GL6; blueprint Charts paragraph
(blueprint: lem-sp-et-proet-coefficient-compatibility). -/
def sumCoefficientIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (e : X ⟶ Y) [Etale e] :
    (Etale.etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory ⋙
        Etale.scalarExtension φ Y ≅
      Etale.scalarExtension φ X ⋙
        (Etale.etaleLowerShriek (ModuleCat.{u + 1} B) e inferInstance).mapDerivedCategory :=
  ((conjugateIsoEquiv
    ((Etale.etaleLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategoryAdjunction.comp
      (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars.{u} Y.smallEtaleTopology φ)))
    ((Adjunction.ofIsRightAdjoint
            (Sheaf.derivedRestrictScalars.{u} X.smallEtaleTopology φ)).comp
      (Etale.etaleLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} B) e inferInstance).mapDerivedCategoryAdjunction)).symm
    (Functor.mapDerivedCategorySquareIso
      (Etale.upperStarRestrictScalarsIsoSheaf φ e))).symm


/-- The canonical compactification change on an etale-origin pro-etale input, using
exactly the specified compact-support site comparison on its two boundaries.
Source: Stacks 0F7I; blueprint normalized site/refinement square
(blueprint: lem-sp-et-proet-coefficient-compatibility). -/
def siteRefinement (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c d : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  (compactSupportSiteComparison A c).app L ≪≫
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.mapIso
      ((Etale.rightDerivedLowerShriekOfCompactificationIso A c d).app L.obj) ≪≫
    ((compactSupportSiteComparison A d).app L).symm

/-- The etale compositor on precisely the three supplied compactifications. The factors
are the existing canonical compactification changes and the proper/open compositor.
Source: Stacks 0F7J; blueprint composition square
(blueprint: lem-sp-et-proet-coefficient-compatibility). -/
def etaleCompositor (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g)) :=
  letI := c.hasCompactification
  letI := d.hasCompactification
  letI := e.hasCompactification
  Functor.isoWhiskerRight (Etale.rightDerivedLowerShriekIso A c)
      (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d) ≪≫
    Functor.isoWhiskerLeft (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f)
      (Etale.rightDerivedLowerShriekIso A d) ≪≫
    Etale.unboundedEtaleLowerShriekCompIso A f g ≪≫
    (Etale.rightDerivedLowerShriekIso A e).symm

/-- The source boundary for composition: apply the two actual site comparisons,
inserting the canonical bounded-below inclusion comparison at the intermediate object.
Source: Stacks 0F7J and 099R; blueprint site/composition square
(blueprint: lem-sp-et-proet-coefficient-compatibility). -/
def compositionSiteBoundary (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (c : Compactification f) (d : Compactification g)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).mapIso
      ((compactSupportSiteComparison A c).app L) ≪≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).mapIso
      ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.mapIso
        ((Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
          (ModuleCat.{u + 1} A) c).app L).symm) ≪≫
    (compactSupportSiteComparison A d).app
      ((Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c).obj L) ≪≫
    (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory.mapIso
      ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).mapIso
        ((Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
          (ModuleCat.{u + 1} A) c).app L))

/-- The pro-etale compositor on etale-origin inputs, transported through the specified
site comparisons. Source: Stacks 0F7J; blueprint site/composition square
(blueprint: lem-sp-et-proet-coefficient-compatibility). -/
def siteCompositor (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g))
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  compositionSiteBoundary A c d L ≪≫
    (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory.mapIso
      ((etaleCompositor A c d e).app L.obj) ≪≫
    ((compactSupportSiteComparison A e).app L).symm


attribute [local irreducible] etaleCoefficientMap proEtaleCoefficientMap
  ProEtale.pbcFixedScalarExtension compactSupportSiteComparison
  DerivedCategory.TStructure.t comparisonUpperStar pbcComparisonReduction
  HasDerivedCategory.ofIsGrothendieckAbelian DerivedCategory
  Functor.leftAdjoint Functor.rightAdjoint
  Functor.mapDerivedCategoryFactors Functor.mapDerivedCategoryFactorsh

set_option backward.isDefEq.respectTransparency false in
private theorem etaleCoefficientMap_eq_compactScalarMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (L : Etale.DerivedCategoryModule A X) :
    etaleCoefficientMap φ c L = (Etale.compactScalarMap φ c).app L := by
  have hi : ((Etale.ExceptionalCoefficients.openIso φ c.i).app L).inv =
      (Etale.properOpenCoefficientOpenIso φ c.i L).inv :=
    Etale.compactScalarOpen_normalization φ c.i L
  have he := Iso.ext_inv hi
  unfold etaleCoefficientMap Etale.compactScalarMap Etale.ExceptionalCoefficients.compactSupportMap
  rw [← he]
  rfl


private theorem etaleProperty_of_domain
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u})
    (L : Etale.DerivedCategoryModule A X)
    (hb : DerivedCategory.TStructure.t.bounded L)
    (hc : ∀ q, IsConstructibleEtaleModuleSheaf
      ((DerivedCategory.homologyFunctor _ q).obj L))
    (ht : ∃ a b : ℤ, a ≤ b ∧ Etale.DerivedCategory.hasTorAmplitudeIn A X a b L) :
    AdjunctionTransfer.etaleProperty A X L := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hb
  let := ha
  let := hb
  obtain ⟨i, j, _, ht⟩ := ht
  exact ⟨⟨hc, min a b, b, min_le_right _ _, fun q hq ↦ hq.elim
    (fun hq ↦ DerivedCategory.isZero_of_isGE L a q
      (lt_of_lt_of_le hq (min_le_left _ _)))
    (fun hq ↦ DerivedCategory.isZero_of_isLE L b q hq)⟩,
    i, j, Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mp ht⟩

private theorem etaleProperty_bounded
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u})
    (L : Etale.DerivedCategoryModule A X) (hL : AdjunctionTransfer.etaleProperty A X L) :
    DerivedCategory.TStructure.t.bounded L := by
  obtain ⟨a, b, _, hz⟩ := hL.1.2
  exact ⟨⟨a, (DerivedCategory.isGE_iff L a).mpr (fun i hi ↦ hz i (.inl hi))⟩,
    ⟨b, (DerivedCategory.isLE_iff L b).mpr (fun i hi ↦ hz i (.inr hi))⟩⟩

private theorem etaleProperty_tor
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u})
    (L : Etale.DerivedCategoryModule A X) (hL : AdjunctionTransfer.etaleProperty A X L) :
    ∃ a b : ℤ, a ≤ b ∧ Etale.DerivedCategory.hasTorAmplitudeIn A X a b L := by
  obtain ⟨a, b, ht⟩ := hL.2
  exact ⟨min a b, b, min_le_right _ _,
    Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mpr
      (ht.mono (min_le_left _ _) le_rfl)⟩

/-- The canonical site/coefficient square, including the invertibility of its two
coefficient arrows. The existential is only a lower-bound proof for the actual scalar
extension; it does not choose a complex or a comparison map.
Source: Stacks 0GL6, 099R; blueprint Charts/Locality, Steps 1--4
(blueprint: lem-sp-et-proet-coefficient-compatibility).

Proof: finiteCompactSupportDomains supplies a lower bound for the actual scalar
extension from the bounded constructible finite-Tor input. The etale coefficient map
is the compact scalar map by open-map normalization; etaleCompactScalarCoherence
makes it invertible. The transportedCompactScalar_site_square equation identifies
the three-factor pro-etale paste with a composite of isomorphisms. Cancelling its
site and scalar/site boundary isomorphisms proves that the actual pro-etale
coefficient arrow is invertible. Together these give the required witness,
invertibility claims and specified equation. -/
theorem etaleProEtaleCoefficientCompatibility
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (ell p : ℕ) [Fact ell.Prime] (_hp : 0 < p) (_hEll : p ≠ ell)
    (k : Type u) [Field k] [CharP k p]
    (_hA : ∃ n : ℕ, ∀ x : A, (ell ^ n) • x = 0)
    (_hB : ∃ n : ℕ, ∀ x : B, (ell ^ n) • x = 0) (φ : A →+* B)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (_hL : AdjunctionTransfer.etaleProperty (ULift.{u + 1, u} A) X L.obj) :
    ∃ hLB : DerivedCategory.TStructure.t.plus ((Etale.scalarExtension (uliftRingHom φ) X).obj
      L.obj),
      IsIso (etaleCoefficientMap (uliftRingHom φ) c L.obj) ∧
      IsIso ((proEtaleCoefficientMap φ c).app
        ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).mapDerivedCategory.obj
          L.obj)) ∧
      (@pbcFixedScalarExtension.{u} Y.ProEt inferInstance
          (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology Y)
          (ULift.{u + 1, u} A) (ULift.{u + 1, u} B) inferInstance inferInstance (uliftRingHom
            φ)).map
          ((compactSupportSiteComparison (ULift.{u + 1, u} A) c).inv.app L) ≫
        (proEtaleCoefficientMap φ c).app
          ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
            X).mapDerivedCategory.obj L.obj) ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) c).map
          ((pbcComparisonReduction.{u} X (uliftRingHom φ)).hom.app L.obj) =
      (pbcComparisonReduction.{u} Y (uliftRingHom φ)).hom.app
          ((Etale.rightDerivedLowerShriekOfCompactification
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).obj L.obj) ≫
        (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) Y).mapDerivedCategory.map
          (etaleCoefficientMap (uliftRingHom φ) c L.obj) ≫
        (compactSupportSiteComparison (ULift.{u + 1, u} B) c).inv.app
          ⟨(Etale.scalarExtension (uliftRingHom φ) X).obj L.obj, hLB⟩ := by
  let RA := ULift.{u + 1, u} A
  let RB := ULift.{u + 1, u} B
  let ψ := uliftRingHom φ
  have hRA : ∃ n : ℕ, ∀ x : RA, (ell ^ n) • x = 0 := by
    obtain ⟨n, hn⟩ := _hA
    exact ⟨n, fun x ↦ ULift.ext _ _ (hn x.down)⟩
  have hRB : ∃ n : ℕ, ∀ x : RB, (ell ^ n) • x = 0 := by
    obtain ⟨n, hn⟩ := _hB
    exact ⟨n, fun x ↦ ULift.ext _ _ (hn x.down)⟩
  have hdom := finiteCompactSupportDomains ell p _hp _hEll.symm k f c hRA hRB ψ L.obj
    (etaleProperty_bounded RA X L.obj _hL) _hL.1.1
    (etaleProperty_tor RA X L.obj _hL)
  have hLB := (hdom.2.1 ⟨X, (Etale.scalarExtension ψ X).obj L.obj⟩ (by simp)).2.2.2.1
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian
    (X ↘ Spec (.of k))
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  let : IsNoetherian X := ⟨⟩
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian
    (Y ↘ Spec (.of k))
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  let : IsNoetherian Y := ⟨⟩
  have he : IsIso (etaleCoefficientMap ψ c L.obj) := by
    rw [etaleCoefficientMap_eq_compactScalarMap]
    exact (Etale.etaleCompactScalarCoherence ψ f c).1 L.obj
  let := he
  have hs := transportedCompactScalar_site_square φ c L hLB
  rw [← etaleCoefficientMap_eq_compactScalarMap] at hs
  rw [← proEtaleCoefficientMap] at hs
  have hp : IsIso ((proEtaleCoefficientMap φ c).app
      ((comparisonUpperStar (ModuleCat.{u + 1} RA) X).mapDerivedCategory.obj L.obj)) := by
    have : IsIso ((liftedScalarExtension φ Y).map
        ((compactSupportSiteComparison RA c).inv.app L) ≫
      (proEtaleCoefficientMap φ c).app
        ((comparisonUpperStar (ModuleCat.{u + 1} RA) X).mapDerivedCategory.obj L.obj) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} RB) c).map
        ((pbcComparisonReduction X ψ).hom.app L.obj)) := by
      rw [hs]
      infer_instance
    have : IsIso ((proEtaleCoefficientMap φ c).app
        ((comparisonUpperStar (ModuleCat.{u + 1} RA) X).mapDerivedCategory.obj L.obj) ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} RB) c).map
          ((pbcComparisonReduction X ψ).hom.app L.obj)) :=
      IsIso.of_isIso_comp_left
        ((liftedScalarExtension φ Y).map ((compactSupportSiteComparison RA c).inv.app L)) _
    exact IsIso.of_isIso_comp_right _
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} RB) c).map
        ((pbcComparisonReduction X ψ).hom.app L.obj))
  exact ⟨hLB, he, hp, hs⟩


private theorem coefficientRefinementTransport
    {C : Type*} [Category C] {Uc Vc Ud Vd Wc Wd Pc Pd Qc Qd : C}
    (ec : Uc ≅ Vc) (ed : Ud ≅ Vd) (cc : Wc ≅ Qc) (cd : Wd ≅ Qd)
    {rc : Vc ⟶ Wc} {rd : Vd ⟶ Wd} {δc : Uc ⟶ Pc} {δd : Ud ⟶ Pd}
    {βc : Pc ⟶ Qc} {βd : Pd ⟶ Qd} {t : Uc ⟶ Ud} {t' : Pc ⟶ Pd} {s : Qc ⟶ Qd}
    (hc : ec.hom ≫ rc = δc ≫ βc ≫ cc.inv)
    (hd : ed.hom ≫ rd = δd ≫ βd ≫ cd.inv)
    (hn : t ≫ δd = δc ≫ t') (hb : t' ≫ βd = βc ≫ s) :
    (ec.inv ≫ t ≫ ed.hom) ≫ rd = rc ≫ cc.hom ≫ s ≫ cd.inv := by
  apply (cancel_epi ec.hom).mp
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [hd, reassoc_of% hc, reassoc_of% hn, reassoc_of% hb]
  simp only [Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Coefficients commute with the canonical compactification change, including a change
through any common refinement, on both sites. The final delta factors express the
pro-etale identity at the retained etale origin of the actual scalar-extended object.
Source: Stacks 0F7I and 0GL6; blueprint Steps 5--7
(blueprint: lem-sp-et-proet-coefficient-compatibility).

Proof: Step 5 pastes the proper counit mates and open tensor units under composition.
Step 6 uses lem-sp-refinement-coefficient-mate for the noncartesian refinement arrow;
its three-constituent theta is the specified canonical refinement. Step 7 applies proper
pushforward and its compositor, then cancels the inverse comparison to give either
orientation. For any common refinement substitute its two squares and cancel their
invertible factors. The canonical cocycle of lem-amb-etale-compact-comparisons proves
independence of that choice. Apply the same site-mate pasting to obtain the pro-etale
square through the specified c; delta only changes the retained scalar-extension origin. -/
theorem etaleProEtaleCoefficientCompatibility_refinement
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (ell p : ℕ) [Fact ell.Prime] (_hp : 0 < p) (_hEll : p ≠ ell)
    (k : Type u) [Field k] [CharP k p]
    (_hA : ∃ n : ℕ, ∀ x : A, (ell ^ n) • x = 0)
    (_hB : ∃ n : ℕ, ∀ x : B, (ell ^ n) • x = 0) (φ : A →+* B)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c d : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (_hL : AdjunctionTransfer.etaleProperty (ULift.{u + 1, u} A) X L.obj) :
    ∃ hLB : DerivedCategory.TStructure.t.plus ((Etale.scalarExtension (uliftRingHom φ) X).obj
      L.obj),
      ((Etale.scalarExtension (uliftRingHom φ) Y).map
          ((Etale.rightDerivedLowerShriekOfCompactificationIso (ULift.{u + 1, u} A) c d).hom.app
            L.obj) ≫
        etaleCoefficientMap (uliftRingHom φ) d L.obj =
      etaleCoefficientMap (uliftRingHom φ) c L.obj ≫
        (Etale.rightDerivedLowerShriekOfCompactificationIso (ULift.{u + 1, u} B) c d).hom.app
          ((Etale.scalarExtension (uliftRingHom φ) X).obj L.obj)) ∧
      ((@pbcFixedScalarExtension.{u} Y.ProEt inferInstance
          (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology Y)
          (ULift.{u + 1, u} A) (ULift.{u + 1, u} B) inferInstance inferInstance (uliftRingHom
            φ)).map
          (siteRefinement (ULift.{u + 1, u} A) c d L).hom ≫
        (proEtaleCoefficientMap φ d).app
          ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
            X).mapDerivedCategory.obj L.obj) ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) d).map
          ((pbcComparisonReduction.{u} X (uliftRingHom φ)).hom.app L.obj) =
      (proEtaleCoefficientMap φ c).app
          ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
            X).mapDerivedCategory.obj L.obj) ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) c).map
          ((pbcComparisonReduction.{u} X (uliftRingHom φ)).hom.app L.obj) ≫
        (siteRefinement (ULift.{u + 1, u} B) c d ⟨(Etale.scalarExtension (uliftRingHom φ) X).obj
          L.obj, hLB⟩).hom)  := by
  obtain ⟨hLB, _, _, hc⟩ := etaleProEtaleCoefficientCompatibility
    ell p _hp _hEll k _hA _hB φ f c L _hL
  obtain ⟨_, _, _, hd⟩ := etaleProEtaleCoefficientCompatibility
    ell p _hp _hEll k _hA _hB φ f d L _hL
  let LB : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) :=
    ⟨(Etale.scalarExtension (uliftRingHom φ) X).obj L.obj, hLB⟩
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian
    (X ↘ Spec (.of k))
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian
    (Y ↘ Spec (.of k))
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  let : IsNoetherian X := ⟨⟩
  let : IsNoetherian Y := ⟨⟩
  have he := (Etale.etaleCompactScalarCoherence (uliftRingHom φ) f c).2.2 d L
    ⟨LB, rfl⟩
  simp only [← etaleCoefficientMap_eq_compactScalarMap] at he
  refine ⟨hLB, he, ?_⟩
  have hn := (pbcComparisonReduction.{u} Y (uliftRingHom φ)).hom.naturality
    ((Etale.rightDerivedLowerShriekOfCompactificationIso (ULift.{u + 1, u} A) c d).hom.app
      L.obj)
  dsimp only [Functor.comp_map] at hn
  have hb := congrArg
    ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) Y).mapDerivedCategory.map) he
  simp only [Functor.map_comp] at hb
  have ht := coefficientRefinementTransport
    ((liftedScalarExtension φ Y).mapIso
      ((compactSupportSiteComparison (ULift.{u + 1, u} A) c).app L).symm)
    ((liftedScalarExtension φ Y).mapIso
      ((compactSupportSiteComparison (ULift.{u + 1, u} A) d).app L).symm)
    ((compactSupportSiteComparison (ULift.{u + 1, u} B) c).app LB)
    ((compactSupportSiteComparison (ULift.{u + 1, u} B) d).app LB) hc hd hn hb
  dsimp only [siteRefinement, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  simp only [Functor.map_comp, Category.assoc] at ht ⊢
  exact ht



set_option backward.isDefEq.respectTransparency false in
private theorem compositionSiteBoundary_eq
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (c : Compactification f) (d : Compactification g)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hFL : DerivedCategory.TStructure.t.plus
      ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj L.obj)) :
    (compositionSiteBoundary A c d L).hom =
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).map
          ((compactSupportSiteComparison A c).hom.app L) ≫
        (compactSupportSiteComparison A d).hom.app ⟨_, hFL⟩ := by
  let κ := (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
    (ModuleCat.{u + 1} A) c).app L
  have hn := (compactSupportSiteComparison A d).hom.naturality
    (ObjectProperty.homMk κ.hom :
      (Etale.rightDerivedLowerShriekOfCompactificationPlus
        (ModuleCat.{u + 1} A) c).obj L ⟶ ⟨_, hFL⟩)
  change
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).map
        ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map κ.hom) ≫
      (compactSupportSiteComparison A d).hom.app ⟨_, hFL⟩ =
    (compactSupportSiteComparison A d).hom.app
        ((Etale.rightDerivedLowerShriekOfCompactificationPlus
          (ModuleCat.{u + 1} A) c).obj L) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory.map
        ((Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} A) d).map κ.hom) at hn
  simp only [compositionSiteBoundary, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom]
  dsimp only [κ, Iso.app_hom] at hn
  rw [← hn]
  let G := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d
  let N := (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory
  have hz : G.map (N.map κ.inv) ≫ G.map (N.map κ.hom) = 𝟙 _ := by
    rw [← G.map_comp, ← N.map_comp, κ.inv_hom_id, N.map_id, G.map_id]
  dsimp only [κ, Iso.app_hom, Iso.app_inv] at hz
  simp only [Iso.app_inv]
  rw [reassoc_of% hz]

private theorem coefficientCompositionChange
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (T : C ⥤ D) (S : E ⥤ F) (G G' : C ⥤ E) (H H' : D ⥤ F)
    (q : G ⋙ S ⟶ T ⋙ H) (q' : G' ⋙ S ⟶ T ⋙ H')
    (d : G ≅ G') (d' : H ≅ H')
    {U V : C} {U' V' : D} (c : U ≅ V) (c' : U' ≅ V')
    {W Z : E} {W' Z' : F} (e : W ≅ Z) (e' : W' ≅ Z')
    (b : T.obj U ⟶ U') (b' : T.obj V ⟶ V')
    (a : S.obj W ⟶ W') (a' : S.obj Z ⟶ Z')
    (m : G'.obj V ⟶ Z) (m' : H'.obj V' ⟶ Z')
    (hc : T.map c.hom ≫ b' = b ≫ c'.hom)
    (hd : S.map (d.hom.app V) ≫ q'.app V = q.app V ≫ d'.hom.app (T.obj V))
    (he : S.map e.hom ≫ a' = a ≫ e'.hom)
    (hm : S.map m ≫ a' = q'.app V ≫ H'.map b' ≫ m') :
    S.map (G.map c.hom ≫ d.hom.app V ≫ m ≫ e.inv) ≫ a =
      q.app U ≫ H.map b ≫ H.map c'.hom ≫ d'.hom.app V' ≫ m' ≫ e'.inv := by
  have hcancel : S.map e.inv ≫ S.map e.hom = 𝟙 _ := by
    rw [← S.map_comp, e.inv_hom_id, S.map_id]
  apply (cancel_mono e'.hom).mp
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hq := q.naturality c.hom
  dsimp only [Functor.comp_map] at hq
  rw [← he, reassoc_of% hcancel, hm, reassoc_of% hd,
    ← d'.hom.naturality_assoc, reassoc_of% hq]
  rw [← H.map_comp_assoc, hc, H.map_comp]
  simp only [Category.assoc]


set_option maxRecDepth 2048 in
set_option backward.isDefEq.respectTransparency false in
private theorem etaleCoefficientComposition
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y Z : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g))
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hLB : DerivedCategory.TStructure.t.plus ((Etale.scalarExtension φ X).obj L.obj))
    (hFL : DerivedCategory.TStructure.t.plus
      ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj L.obj))
    (hF'L : DerivedCategory.TStructure.t.plus
      ((Etale.scalarExtension φ Y).obj
        ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj
          L.obj))) :
    (Etale.scalarExtension φ Z).map ((etaleCompositor A c d e).hom.app L.obj) ≫
        etaleCoefficientMap φ e L.obj =
      etaleCoefficientMap φ d
          ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj
            L.obj) ≫
        (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) d).map
          (etaleCoefficientMap φ c L.obj) ≫
        (etaleCompositor B c d e).hom.app ((Etale.scalarExtension φ X).obj L.obj) := by
  let := c.hasCompactification
  let := d.hasCompactification
  let := e.hasCompactification
  let c' := HasCompactification.compactification f
  let d' := HasCompactification.compactification g
  let e' := HasCompactification.compactification (f ≫ g)
  let LB : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) := ⟨_, hLB⟩
  let FL : DerivedCategory.Plus
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    ⟨_, DerivedCategory.TStructure.t.plus.prop_of_iso
      ((Etale.rightDerivedLowerShriekIso A c).app L.obj) hFL⟩
  let F'LB : DerivedCategory.Plus
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B)) :=
    ⟨_, DerivedCategory.TStructure.t.plus.prop_of_iso
      ((Etale.scalarExtension φ Y).mapIso
        ((Etale.rightDerivedLowerShriekIso A c).app L.obj)) hF'L⟩
  have hc := (Etale.etaleCompactScalarCoherence φ f c).2.2 c' L ⟨LB, rfl⟩
  have hd := (Etale.etaleCompactScalarCoherence φ g d).2.2 d' FL ⟨F'LB, rfl⟩
  have he := (Etale.etaleCompactScalarCoherence φ (f ≫ g) e).2.2 e' L ⟨LB, rfl⟩
  have hm := Etale.etaleCompactScalarComposition φ f g L ⟨LB, rfl⟩
  have h := coefficientCompositionChange
    (Etale.scalarExtension φ Y) (Etale.scalarExtension φ Z)
    (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d)
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) g)
    (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) d)
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} B) g)
    (Etale.compactScalarMap φ d) (Etale.compactScalarChosenMap φ g)
    (Etale.rightDerivedLowerShriekIso A d) (Etale.rightDerivedLowerShriekIso B d)
    ((Etale.rightDerivedLowerShriekIso A c).app L.obj)
    ((Etale.rightDerivedLowerShriekIso B c).app ((Etale.scalarExtension φ X).obj L.obj))
    ((Etale.rightDerivedLowerShriekIso A e).app L.obj)
    ((Etale.rightDerivedLowerShriekIso B e).app ((Etale.scalarExtension φ X).obj L.obj))
    ((Etale.compactScalarMap φ c).app L.obj)
    ((Etale.compactScalarChosenMap φ f).app L.obj)
    ((Etale.compactScalarMap φ e).app L.obj)
    ((Etale.compactScalarChosenMap φ (f ≫ g)).app L.obj)
    ((Etale.unboundedEtaleLowerShriekCompIso A f g).hom.app L.obj)
    ((Etale.unboundedEtaleLowerShriekCompIso B f g).hom.app
      ((Etale.scalarExtension φ X).obj L.obj)) hc hd he hm
  simp only [etaleCoefficientMap_eq_compactScalarMap]
  simpa only [etaleCompositor, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.app_hom, Iso.app_inv,
    Category.assoc] using h


private theorem coefficientSquareForward
    {C : Type*} [Category C] {U V W P Q R : C}
    (e : U ≅ V) (c : Q ≅ R) {b : V ⟶ W} {d : W ⟶ Q}
    {δ : U ⟶ P} {β : P ⟶ R}
    (h : e.hom ≫ b ≫ d = δ ≫ β ≫ c.inv) :
    e.inv ≫ δ ≫ β = b ≫ d ≫ c.hom := by
  rw [← cancel_epi e.hom]
  simp only [Iso.hom_inv_id_assoc]
  rw [reassoc_of% h, c.inv_hom_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
private theorem coefficientVerticalForward
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (S : C ⥤ D) (T : E ⥤ F) (P : C ⥤ E) (Q : D ⥤ F)
    (b : P ⋙ T ⟶ S ⋙ Q)
    {U V : C} {W X Y : D} {Z : E} {R I : F}
    (c : U ≅ V) (d : P.obj V ≅ Z) (e : W ≅ Y)
    (a : Q.obj X ≅ R) (a' : Q.obj Y ≅ I)
    (δ : S.obj V ⟶ X) (β : X ⟶ Y) (r : S.obj U ⟶ W)
    (ω : T.obj Z ⟶ R) (n : R ⟶ I)
    (hc : S.map c.hom ≫ δ ≫ β = r ≫ e.hom)
    (hd : T.map d.hom ≫ ω = b.app V ≫ Q.map δ ≫ a.hom)
    (hn : Q.map β ≫ a'.hom = a.hom ≫ n) :
    T.map (P.map c.hom ≫ d.hom) ≫ ω ≫ n =
      b.app U ≫ Q.map r ≫ Q.map e.hom ≫ a'.hom := by
  have hb := b.naturality c.hom
  dsimp only [Functor.comp_map] at hb
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hd, ← hn, reassoc_of% hb]
  rw [← Q.map_comp_assoc, ← Q.map_comp_assoc, Category.assoc, hc, Q.map_comp]
  simp only [Category.assoc]

set_option maxRecDepth 2048 in
set_option backward.isDefEq.respectTransparency false in
/-- The same coefficient maps respect geometric composition, on each site and for any
three compactifications. Scalar restriction need not be faithful in the derived category.
Source: Stacks 0F7J and 0GL6; blueprint Steps 5, 6, 8 and 9
(blueprint: lem-sp-et-proet-coefficient-compatibility).

Proof: Step 8 chooses the compatible compactification tower of
lem-cbc-compactifiable-compatible-tower. Its compositor is the proper/open interchange
followed by proper and open composition. Step 6 uses lem-sp-proper-open-coefficient-mate
for the cartesian square in that tower. Step 5 commutes coefficients past the proper and
open compositors by counit transposition and the summand tensor calculation. Pasting
gives the composition equation. Step 9 conjugates to arbitrary compactifications using
the refinement square just stated; inverse refinement factors cancel. The site versions
of the same constituent squares give the displayed pro-etale identity. Inserting the
invertible delta at the final input is exactly the retained etale-origin convention. -/
theorem etaleProEtaleCoefficientCompatibility_composition
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (ell p : ℕ) [Fact ell.Prime] (_hp : 0 < p) (_hEll : p ≠ ell)
    (k : Type u) [Field k] [CharP k p]
    (_hA : ∃ n : ℕ, ∀ x : A, (ell ^ n) • x = 0)
    (_hB : ∃ n : ℕ, ∀ x : B, (ell ^ n) • x = 0) (φ : A →+* B)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {Z : Scheme.{u}} [Z.Over (Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    (g : Y ⟶ Z) [g.IsOver (Spec (.of k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g))
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (_hL : AdjunctionTransfer.etaleProperty (ULift.{u + 1, u} A) X L.obj) :
    ∃ hLB : DerivedCategory.TStructure.t.plus ((Etale.scalarExtension (uliftRingHom φ) X).obj
      L.obj),
      ((Etale.scalarExtension (uliftRingHom φ) Z).map ((etaleCompositor (ULift.{u + 1, u} A) c d
        e).hom.app L.obj) ≫
        etaleCoefficientMap (uliftRingHom φ) e L.obj =
      etaleCoefficientMap (uliftRingHom φ) d
          ((Etale.rightDerivedLowerShriekOfCompactification
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).obj L.obj) ≫
        (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (ULift.{u + 1, u}
          B)) d).map
          (etaleCoefficientMap (uliftRingHom φ) c L.obj) ≫
        (etaleCompositor (ULift.{u + 1, u} B) c d e).hom.app ((Etale.scalarExtension
          (uliftRingHom φ) X).obj L.obj)) ∧
      ((@pbcFixedScalarExtension.{u} Z.ProEt inferInstance
          (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology Z)
          (ULift.{u + 1, u} A) (ULift.{u + 1, u} B) inferInstance inferInstance (uliftRingHom
            φ)).map
          (siteCompositor (ULift.{u + 1, u} A) c d e L).hom ≫
        (proEtaleCoefficientMap φ e).app
          ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
            X).mapDerivedCategory.obj L.obj) ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) e).map
          ((pbcComparisonReduction.{u} X (uliftRingHom φ)).hom.app L.obj) =
      (proEtaleCoefficientMap φ d).app
          ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
            c).obj
            ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
              X).mapDerivedCategory.obj L.obj)) ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) d).map
          ((proEtaleCoefficientMap φ c).app
            ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
              X).mapDerivedCategory.obj L.obj)) ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) d).map
          ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (ULift.{u + 1, u} B))
            c).map
            ((pbcComparisonReduction.{u} X (uliftRingHom φ)).hom.app L.obj)) ≫
        (siteCompositor (ULift.{u + 1, u} B) c d e ⟨(Etale.scalarExtension (uliftRingHom φ)
          X).obj L.obj, hLB⟩).hom) := by
  let RA := ULift.{u + 1, u} A
  let RB := ULift.{u + 1, u} B
  let ψ := uliftRingHom φ
  have hRA : ∃ n : ℕ, ∀ x : RA, (ell ^ n) • x = 0 := by
    obtain ⟨n, hn⟩ := _hA
    exact ⟨n, fun x ↦ ULift.ext _ _ (hn x.down)⟩
  have hRB : ∃ n : ℕ, ∀ x : RB, (ell ^ n) • x = 0 := by
    obtain ⟨n, hn⟩ := _hB
    exact ⟨n, fun x ↦ ULift.ext _ _ (hn x.down)⟩
  obtain ⟨hLB, _, _, hc⟩ := etaleProEtaleCoefficientCompatibility
    ell p _hp _hEll k _hA _hB φ f c L _hL
  obtain ⟨_, _, _, he⟩ := etaleProEtaleCoefficientCompatibility
    ell p _hp _hEll k _hA _hB φ (f ≫ g) e L _hL
  obtain ⟨hFL, hFAB, hFBL, hprop⟩ :
      DerivedCategory.TStructure.t.plus
          ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} RA) c).obj
            L.obj) ∧
      DerivedCategory.TStructure.t.plus ((Etale.scalarExtension ψ Y).obj
          ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} RA) c).obj
            L.obj)) ∧
      DerivedCategory.TStructure.t.plus
          ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} RB) c).obj
            ((Etale.scalarExtension ψ X).obj L.obj)) ∧
      AdjunctionTransfer.etaleProperty RA Y
          ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} RA) c).obj
            L.obj) := by
    have hdom := finiteCompactSupportDomains ell p _hp _hEll.symm k f c hRA hRB ψ L.obj
      (etaleProperty_bounded RA X L.obj _hL) _hL.1.1
      (etaleProperty_tor RA X L.obj _hL)
    have hFA := hdom.1
      ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} RA) c).obj
        L.obj) (by simp)
    have hFAB := hdom.2.1
      ⟨Y, (Etale.scalarExtension ψ Y).obj
        ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} RA) c).obj
          L.obj)⟩ (by simp)
    have hFB := hdom.2.1
      ⟨Y, (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} RB) c).obj
        ((Etale.scalarExtension ψ X).obj L.obj)⟩ (by simp)
    exact ⟨hFA.2.2.2.1, hFAB.2.2.2.1, hFB.2.2.2.1,
      etaleProperty_of_domain RA Y _ hFA.1 hFA.2.1 hFA.2.2.1⟩
  let FL : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} RA)) :=
    ⟨_, hFL⟩
  let LB : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} RB)) :=
    ⟨_, hLB⟩
  let FLB : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} RB)) :=
    ⟨_, hFAB⟩
  let FBL : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} RB)) :=
    ⟨_, hFBL⟩
  obtain ⟨_, _, _, hd⟩ := etaleProEtaleCoefficientCompatibility
    ell p _hp _hEll k _hA _hB φ g d FL hprop
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian
    (X ↘ Spec (.of k))
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  let : IsNoetherian X := ⟨⟩
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian
    (Y ↘ Spec (.of k))
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  let : IsNoetherian Y := ⟨⟩
  let : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian
    (Z ↘ Spec (.of k))
  let : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace (Z ↘ Spec (.of k))
  let : IsNoetherian Z := ⟨⟩
  have hEt := etaleCoefficientComposition ψ f g c d e L hLB hFL hFAB
  refine ⟨hLB, hEt, ?_⟩
  let T := liftedScalarExtension φ Z
  let N := (comparisonUpperStar (ModuleCat.{u + 1} RB) Z).mapDerivedCategory
  let G := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} RB) d
  have hc' := coefficientSquareForward
    ((liftedScalarExtension φ Y).mapIso ((compactSupportSiteComparison RA c).app L).symm)
    ((compactSupportSiteComparison RB c).app LB) hc
  have hd' := coefficientSquareForward
    (T.mapIso ((compactSupportSiteComparison RA d).app FL).symm)
    ((compactSupportSiteComparison RB d).app FLB) hd
  simp only [Functor.mapIso_inv, Iso.symm_inv, Iso.app_hom] at hc' hd'
  have hnδ := (pbcComparisonReduction.{u} Z ψ).hom.naturality
    ((etaleCompositor RA c d e).hom.app L.obj)
  change T.map
      ((comparisonUpperStar (ModuleCat.{u + 1} RA) Z).mapDerivedCategory.map
        ((etaleCompositor RA c d e).hom.app L.obj)) ≫
      (pbcComparisonReduction Z ψ).hom.app
        ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} RA) e).obj
          L.obj) =
    (pbcComparisonReduction Z ψ).hom.app
        ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} RA) d).obj
          FL.obj) ≫
      N.map ((Etale.scalarExtension ψ Z).map
        ((etaleCompositor RA c d e).hom.app L.obj)) at hnδ
  have hnC := (compactSupportSiteComparison RB d).hom.naturality
    (ObjectProperty.homMk (etaleCoefficientMap ψ c L.obj) : FLB ⟶ FBL)
  have hv := coefficientVerticalForward
    (liftedScalarExtension φ Y) T
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} RA) d) G
    (proEtaleCoefficientMap φ d)
    ((compactSupportSiteComparison RA c).app L)
    ((compactSupportSiteComparison RA d).app FL)
    ((compactSupportSiteComparison RB c).app LB)
    ((compactSupportSiteComparison RB d).app FLB)
    ((compactSupportSiteComparison RB d).app FBL)
    ((pbcComparisonReduction Y ψ).hom.app FL.obj)
    ((comparisonUpperStar (ModuleCat.{u + 1} RB) Y).mapDerivedCategory.map
      (etaleCoefficientMap ψ c L.obj))
    ((proEtaleCoefficientMap φ c).app
        ((comparisonUpperStar (ModuleCat.{u + 1} RA) X).mapDerivedCategory.obj L.obj) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} RB) c).map
        ((pbcComparisonReduction X ψ).hom.app L.obj))
    ((pbcComparisonReduction Z ψ).hom.app
        ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} RA) d).obj
          FL.obj) ≫ N.map (etaleCoefficientMap ψ d FL.obj))
    (N.map ((Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} RB) d).map (etaleCoefficientMap ψ c L.obj)))
    (by simpa only [Iso.app_hom, Category.assoc] using hc')
    (by simpa only [Iso.app_hom, Functor.comp_obj, ObjectProperty.ι_obj,
      FL, ψ, N, T, G, Category.assoc] using hd')
    (by exact hnC)
  have hNEt := congrArg N.map hEt
  simp only [Functor.map_comp] at hNEt
  have hbA := compositionSiteBoundary_eq RA c d L hFL
  have hbB := compositionSiteBoundary_eq RB c d LB hFBL
  have hv' : T.map (compositionSiteBoundary RA c d L).hom ≫
      (pbcComparisonReduction Z ψ).hom.app
        ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} RA) d).obj
          FL.obj) ≫ N.map (etaleCoefficientMap ψ d FL.obj) ≫
      N.map ((Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} RB) d).map (etaleCoefficientMap ψ c L.obj)) =
    (proEtaleCoefficientMap φ d).app
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} RA) c).obj
          ((comparisonUpperStar (ModuleCat.{u + 1} RA) X).mapDerivedCategory.obj L.obj)) ≫
      G.map ((proEtaleCoefficientMap φ c).app
        ((comparisonUpperStar (ModuleCat.{u + 1} RA) X).mapDerivedCategory.obj L.obj)) ≫
      G.map ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} RB) c).map
        ((pbcComparisonReduction X ψ).hom.app L.obj)) ≫
      (compositionSiteBoundary RB c d LB).hom := by
    rw [hbA, hbB]
    simpa only [Functor.map_comp, Category.assoc, Iso.app_hom,
      Functor.comp_obj, ObjectProperty.ι_obj, FL, FBL, LB, G] using hv
  have hv'' : T.map (compositionSiteBoundary RA c d L).hom ≫
      (pbcComparisonReduction Z ψ).hom.app
        ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} RA) d).obj
          FL.obj) ≫ N.map (etaleCoefficientMap ψ d FL.obj) ≫
      N.map ((Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} RB) d).map (etaleCoefficientMap ψ c L.obj)) ≫
      (compositionSiteBoundary RB c d LB).inv =
    (proEtaleCoefficientMap φ d).app
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} RA) c).obj
          ((comparisonUpperStar (ModuleCat.{u + 1} RA) X).mapDerivedCategory.obj L.obj)) ≫
      G.map ((proEtaleCoefficientMap φ c).app
        ((comparisonUpperStar (ModuleCat.{u + 1} RA) X).mapDerivedCategory.obj L.obj)) ≫
      G.map ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} RB) c).map
        ((pbcComparisonReduction X ψ).hom.app L.obj)) := by
    have h := congrArg (fun t ↦ t ≫ (compositionSiteBoundary RB c d LB).inv) hv'
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h
  have ht := coefficientRefinementTransport
    (T.mapIso (compositionSiteBoundary RA c d L).symm)
    (T.mapIso ((compactSupportSiteComparison RA e).app L).symm)
    (compositionSiteBoundary RB c d LB)
    ((compactSupportSiteComparison RB e).app LB)
    (rc := (proEtaleCoefficientMap φ d).app
      ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} RA) c).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} RA) X).mapDerivedCategory.obj L.obj)) ≫
      G.map ((proEtaleCoefficientMap φ c).app
        ((comparisonUpperStar (ModuleCat.{u + 1} RA) X).mapDerivedCategory.obj L.obj)) ≫
      G.map ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} RB) c).map
        ((pbcComparisonReduction X ψ).hom.app L.obj)))
    (δc := (pbcComparisonReduction Z ψ).hom.app
      ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} RA) d).obj
        FL.obj))
    (βc := N.map (etaleCoefficientMap ψ d FL.obj) ≫
      N.map ((Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} RB) d).map (etaleCoefficientMap ψ c L.obj)))
    (s := N.map ((etaleCompositor RB c d e).hom.app LB.obj))
    (by
      apply ((T.mapIso (compositionSiteBoundary RA c d L)).inv_comp_eq).mpr
      simpa only [Functor.mapIso_hom, Category.assoc] using hv''.symm)
    he hnδ (by simpa only [Category.assoc, FL, LB] using hNEt)
  dsimp only [siteCompositor, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Iso.symm_inv, Iso.app_hom, Iso.app_inv]
  simp only [Functor.map_comp, Category.assoc] at ht ⊢
  exact ht

/-- Evaluate the recorded normalized sum comparison, supplying the Noetherian and compact
structures derived from finite type over the field. No extra scheme hypothesis is imposed.
Source: SGA 4 XVII 6.2.11; blueprint etale-sum clause
(blueprint: lem-sp-et-proet-coefficient-compatibility). -/
def normalizedSumComparison (A : Type (u + 1)) [CommRing A]
    (k : Type u) [Field k]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (N : Etale.EtaleCompactSupportNormalization A) (e : X ⟶ Y) [Etale e] [IsSeparated e]
    (c : Compactification e) :
    Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
      (Etale.etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory :=
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian
    (X ↘ Spec (.of k))
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian
    (Y ↘ Spec (.of k))
  letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  N.comparison e c

/-- The compact-support coefficient map agrees with summandwise tensor extension for a
separated etale morphism. The normalization records fix the maps by their graph-extension
and derived-representative equations, so no arbitrary endpoint isomorphism is assumed.
Source: Stacks 0GL6 and 03S6; blueprint Step 10
(blueprint: lem-sp-et-proet-coefficient-compatibility).

Proof: lem-asd-etale-compact-support-normalization sends a properly supported section to
its labelled sheet components and makes j!H acyclic for the proper factor. On the bounded
flat model P of Step 1, sum extension preserves flatness and K-flatness by the slice tensor
formula, exactness of sum extension and exact inverse image. The same applies to j!P.
Apply lem-sp-acyclic-flat-proper-coefficient-model to j!P: the proper coefficient mate is
the sheaf projection map. Composing with the open tensor comparison sends each labelled
section tensor b to the same labelled section with coefficient b, in both orders.
The graph normalizations retain the label, so the complexes give equal derived maps.
lem-amb-etale-sum-stalks includes empty fibres, without requiring finitely many lifts
on each test object. -/
theorem etaleProEtaleCoefficientCompatibility_sum
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (ell p : ℕ) [Fact ell.Prime] (_hp : 0 < p) (_hEll : p ≠ ell)
    (k : Type u) [Field k] [CharP k p]
    (_hA : ∃ n : ℕ, ∀ x : A, (ell ^ n) • x = 0)
    (_hB : ∃ n : ℕ, ∀ x : B, (ell ^ n) • x = 0) (φ : A →+* B)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [Etale f] (c : Compactification f)
    (NA : Etale.EtaleCompactSupportNormalization A)
    (NB : Etale.EtaleCompactSupportNormalization B)
    (L : Etale.DerivedCategoryModule A X)
    (_hL : AdjunctionTransfer.etaleProperty A X L) :
    etaleCoefficientMap φ c L ≫
        (normalizedSumComparison B k NB f c).hom.app ((Etale.scalarExtension φ X).obj L) =
      (Etale.scalarExtension φ Y).map ((normalizedSumComparison A k NA f c).hom.app L) ≫
        (sumCoefficientIso φ f).hom.app L := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian
    (X ↘ Spec (.of k))
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian
    (Y ↘ Spec (.of k))
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  let : IsNoetherian X := ⟨⟩
  let : IsNoetherian Y := ⟨⟩
  obtain ⟨a, b, hab, ht⟩ := etaleProperty_tor A X L _hL
  obtain ⟨P, hf, hc, hz, ⟨eP⟩⟩ :=
    (Etale.hasTorAmplitudeIn_iff_exists_finiteValueConstructibleModel
      A X a b hab L _hL.1).mp ht
  have hf' : ∀ q : ℤ, exactFunctor _ _ (MonoidalCategory.tensorRight (P.X q)) :=
    fun q ↦ (hf q).2
  have hcomp := Etale.etaleSumCoefficientComputation φ f c P ⟨a, b, hz⟩ hf'
  have hrep := hcomp.2.2.2.2.2.2.2.2.2.2.1
  let := hrep
  have hcalc := hcomp.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hsum := Etale.etaleSumScalarRepresentative φ f P a b hz hf'
  change (Etale.scalarExtension φ Y).map _ ≫ _ ≫ _ =
    (sumCoefficientIso φ f).hom.app (DerivedCategory.Q.obj P) ≫ _ ≫ _ at hsum
  have hNA := Etale.normalization_boundary A NA f c P a b hz
  have hzB : ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((Etale.coefficientExtendedComplex φ X P).X q) := by
    intro q hq
    exact (etaleSheafExtendScalars φ X).map_isZero (hz q hq)
  have hNB := Etale.normalization_boundary B NB f c
    (Etale.coefficientExtendedComplex φ X P) a b hzB
  have hmodel :
      (Etale.scalarExtension φ Y).map ((NA.comparison f c).inv.app
          (DerivedCategory.Q.obj P)) ≫ etaleCoefficientMap φ c (DerivedCategory.Q.obj P) =
        (sumCoefficientIso φ f).hom.app (DerivedCategory.Q.obj P) ≫
          (NB.comparison f c).inv.app
            ((Etale.scalarExtension φ X).obj (DerivedCategory.Q.obj P)) := by
    apply (cancel_mono ((Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} B) c).map (Etale.scalarExtensionRepresentative φ X P))).mp
    have h := congrArg (fun z ↦
      (Etale.scalarExtension φ Y).map
        ((Etale.etaleLowerShriek (ModuleCat.{u + 1} A) f
          inferInstance).mapDerivedCategoryFactors.hom.app
          P) ≫ z) hcalc
    dsimp only [etaleCoefficientMap, Etale.properCoefficientMap] at *
    simp only [Category.assoc] at h ⊢
    rw [← Functor.map_comp_assoc, hNA] at h
    rw [reassoc_of% hsum, hNB] at h
    have hn := (NB.comparison f c).inv.naturality
      (Etale.scalarExtensionRepresentative φ X P)
    dsimp only [Functor.comp_map] at hn
    rw [hn] at h
    simpa only [etaleCoefficientMap, Category.assoc,
      Etale.rightDerivedLowerShriekOfCompactification, Etale.rightDerivedLowerStar,
      Functor.comp_map] using h
  have hQP :
      etaleCoefficientMap φ c (DerivedCategory.Q.obj P) ≫
          (NB.comparison f c).hom.app
            ((Etale.scalarExtension φ X).obj (DerivedCategory.Q.obj P)) =
        (Etale.scalarExtension φ Y).map
            ((NA.comparison f c).hom.app (DerivedCategory.Q.obj P)) ≫
          (sumCoefficientIso φ f).hom.app (DerivedCategory.Q.obj P) := by
    apply (cancel_epi ((Etale.scalarExtension φ Y).map
      ((NA.comparison f c).inv.app (DerivedCategory.Q.obj P)))).mp
    simp only [← Category.assoc, hmodel]
    simp only [Category.assoc, Iso.inv_hom_id_app,
      ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
    exact Category.comp_id _
  let α := Etale.compactScalarMap φ c ≫
    Functor.whiskerLeft (Etale.scalarExtension φ X) (NB.comparison f c).hom
  let β := Functor.whiskerRight (NA.comparison f c).hom (Etale.scalarExtension φ Y) ≫
    (sumCoefficientIso φ f).hom
  have hQP' : α.app (DerivedCategory.Q.obj P) = β.app (DerivedCategory.Q.obj P) := by
    simpa only [α, β, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, ← etaleCoefficientMap_eq_compactScalarMap] using hQP
  have hL : α.app L = β.app L := by
    apply (cancel_epi
      ((Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} A) c ⋙ Etale.scalarExtension φ Y).map eP.hom)).mp
    rw [α.naturality eP.hom, β.naturality eP.hom, hQP']
  simpa only [α, β, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, ← etaleCoefficientMap_eq_compactScalarMap,
    normalizedSumComparison] using hL

private theorem coefficientCounitTransport
    {C : Type*} [Category C] {U V W D E P Q R S F : C}
    (e : U ≅ V) (c₀ : D ≅ Q) (c₁ : E ≅ R) (z : F ≅ S)
    {b : V ⟶ W} {d : W ⟶ D} {a : D ⟶ E} {δ : U ⟶ P}
    {β : P ⟶ Q} {a' : Q ⟶ R} {ε : R ⟶ S} {r : P ⟶ S} {t : U ⟶ F}
    (hs : e.hom ≫ b ≫ d = δ ≫ β ≫ c₀.inv)
    (hn : a ≫ c₁.hom = c₀.hom ≫ a')
    (hc : β ≫ a' ≫ ε = r) (hd : t ≫ z.hom = δ ≫ r) :
    b ≫ d ≫ a ≫ c₁.hom ≫ ε ≫ z.inv = e.inv ≫ t := by
  apply (cancel_epi e.hom).mp
  rw [reassoc_of% hs, reassoc_of% hn]
  simp only [Iso.inv_hom_id_assoc]
  rw [reassoc_of% hc, ← reassoc_of% hd]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Transport of an actual etale adjunction counit carries its coefficient identity to
the identity for the named pro-etale coefficient map. The two c-inverses in the paper
are `compactSupportSiteComparison.hom` with the existing library's opposite orientation.
The final delta removes only the output coefficient/site identification.
Source: blueprint Step 11, using det-sp-et-proet-adjunction-transfer's counit formula
(blueprint: lem-sp-et-proet-coefficient-compatibility).

Proof: solve the site/coefficient square of Steps 1--4 for the b-inverse. Substitute it
in coefficient extension of the transported A-counit. Naturality of delta moves that
counit across the tensor/site comparison. Apply the assumed etale coefficient-counit
identity. Naturality of the B-site comparison moves the right-functor comparison across
c_B-inverse. What remains is precisely the transported B-counit after compact support of
the transported right-functor comparison. The displayed form avoids inverses of beta and
b by precomposing with b; their invertibility is in the first statement. This substitution
requires no admissibility theorem for arbitrary finite rings. -/
theorem etaleProEtaleCoefficientCompatibility_counit
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (ell p : ℕ) [Fact ell.Prime] (_hp : 0 < p) (_hEll : p ≠ ell)
    (k : Type u) [Field k] [CharP k p]
    (_hA : ∃ n : ℕ, ∀ x : A, (ell ^ n) • x = 0)
    (_hB : ∃ n : ℕ, ∀ x : B, (ell ^ n) • x = 0) (φ : A →+* B)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (HA : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) Y ⥤ Etale.DerivedCategoryModule
      (ULift.{u + 1, u} A) X)
    (HB : Etale.DerivedCategoryModule (ULift.{u + 1, u} B) Y ⥤ Etale.DerivedCategoryModule
      (ULift.{u + 1, u} B) X)
    (adjA : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (ULift.{u + 1, u}
      A)) c ⊣ HA)
    (adjB : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (ULift.{u + 1, u}
      B)) c ⊣ HB)
    (N : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) Y)
    (hHA : AdjunctionTransfer.etaleProperty (ULift.{u + 1, u} A) X (HA.obj N))
    (hHB : AdjunctionTransfer.etaleProperty (ULift.{u + 1, u} B) X (HB.obj
      ((Etale.scalarExtension (uliftRingHom φ) Y).obj N)))
    (a : (Etale.scalarExtension (uliftRingHom φ) X).obj (HA.obj N) ⟶
      HB.obj ((Etale.scalarExtension (uliftRingHom φ) Y).obj N))
    (_hCounit : etaleCoefficientMap (uliftRingHom φ) c (HA.obj N) ≫
        (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (ULift.{u + 1, u}
          B)) c).map a ≫
        adjB.counit.app ((Etale.scalarExtension (uliftRingHom φ) Y).obj N) =
      (Etale.scalarExtension (uliftRingHom φ) Y).map (adjA.counit.app N)) :
    (proEtaleCoefficientMap φ c).app
        ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).mapDerivedCategory.obj
          (HA.obj N)) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) c).map
        ((pbcComparisonReduction.{u} X (uliftRingHom φ)).hom.app (HA.obj N) ≫
          (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B))
            X).mapDerivedCategory.map a) ≫
      (compactSupportSiteComparison (ULift.{u + 1, u} B) c).hom.app
        ((AdjunctionTransfer.etaleToPlus (ULift.{u + 1, u} B) X).obj
          ⟨HB.obj ((Etale.scalarExtension (uliftRingHom φ) Y).obj N), hHB⟩) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) Y).mapDerivedCategory.map
        (adjB.counit.app ((Etale.scalarExtension (uliftRingHom φ) Y).obj N)) ≫
      (pbcComparisonReduction.{u} Y (uliftRingHom φ)).inv.app N =
    (@pbcFixedScalarExtension.{u} Y.ProEt inferInstance
          (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology Y)
          (ULift.{u + 1, u} A) (ULift.{u + 1, u} B) inferInstance inferInstance (uliftRingHom
            φ)).map
      ((compactSupportSiteComparison (ULift.{u + 1, u} A) c).hom.app
          ((AdjunctionTransfer.etaleToPlus (ULift.{u + 1, u} A) X).obj ⟨HA.obj N, hHA⟩) ≫
        (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Y).mapDerivedCategory.map
          (adjA.counit.app N))  := by
  let LA := (AdjunctionTransfer.etaleToPlus (ULift.{u + 1, u} A) X).obj ⟨HA.obj N, hHA⟩
  let MB := (AdjunctionTransfer.etaleToPlus (ULift.{u + 1, u} B) X).obj
    ⟨HB.obj ((Etale.scalarExtension (uliftRingHom φ) Y).obj N), hHB⟩
  obtain ⟨hLB, _, _, hs⟩ := etaleProEtaleCoefficientCompatibility
    ell p _hp _hEll k _hA _hB φ f c LA hHA
  let LB : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) :=
    ⟨(Etale.scalarExtension (uliftRingHom φ) X).obj (HA.obj N), hLB⟩
  have hn := (compactSupportSiteComparison (ULift.{u + 1, u} B) c).hom.naturality
    (ObjectProperty.homMk a : LB ⟶ MB)
  dsimp only [Functor.comp_map] at hn
  have hc := congrArg
    ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) Y).mapDerivedCategory.map)
    _hCounit
  simp only [Functor.map_comp] at hc
  have hd := (pbcComparisonReduction.{u} Y (uliftRingHom φ)).hom.naturality
    (adjA.counit.app N)
  dsimp only [Functor.comp_map] at hd
  have ht := coefficientCounitTransport
    ((liftedScalarExtension φ Y).mapIso
      ((compactSupportSiteComparison (ULift.{u + 1, u} A) c).app LA).symm)
    ((compactSupportSiteComparison (ULift.{u + 1, u} B) c).app LB)
    ((compactSupportSiteComparison (ULift.{u + 1, u} B) c).app MB)
    ((pbcComparisonReduction.{u} Y (uliftRingHom φ)).app N) hs hn hc hd
  simp only [Functor.map_comp, Category.assoc]
  exact ht

set_option backward.isDefEq.respectTransparency false in
private theorem openCoefficientInverse_naturality
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X T : Scheme.{u}} (j : X ⟶ T) [IsOpenImmersion j]
    {L M : Etale.DerivedCategoryModule A X} (a : L ⟶ M) :
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.map
        ((Etale.scalarExtension φ X).map a) ≫ Etale.properOpenCoefficientOpenInverse φ j M =
      Etale.properOpenCoefficientOpenInverse φ j L ≫ (Etale.scalarExtension φ T).map
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.map a) := by
  unfold Etale.properOpenCoefficientOpenInverse
  apply Adjunction.homEquiv_naturality_right_square
  have hu := (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) j).unit.naturality a
  dsimp only [Functor.id_map, Functor.comp_map] at hu
  rw [← Category.assoc, ← Functor.map_comp, hu, Functor.map_comp, Category.assoc]
  rw [Category.assoc]
  exact congrArg ((Etale.scalarExtension φ X).map
    ((Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) j).unit.app L) ≫ ·)
    ((Etale.properOpenCoefficientPullbackIso φ j).inv.naturality
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.map a))

set_option backward.isDefEq.respectTransparency false in
private theorem openCoefficientHom_naturality
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X T : Scheme.{u}} (j : X ⟶ T) [IsOpenImmersion j]
    {L M : Etale.DerivedCategoryModule A X} (a : L ⟶ M) :
    (Etale.scalarExtension φ T).map
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.map a) ≫
        (Etale.properOpenCoefficientOpenIso φ j M).hom =
      (Etale.properOpenCoefficientOpenIso φ j L).hom ≫
        (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.map
          ((Etale.scalarExtension φ X).map a) := by
  have h :
      (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.map
          ((Etale.scalarExtension φ X).map a) ≫
          (Etale.properOpenCoefficientOpenIso φ j M).inv =
        (Etale.properOpenCoefficientOpenIso φ j L).inv ≫
          (Etale.scalarExtension φ T).map
            ((Etale.openImmersionLowerShriek
              (ModuleCat.{u + 1} A) j).mapDerivedCategory.map a) :=
    openCoefficientInverse_naturality φ j a
  apply (cancel_mono (Etale.properOpenCoefficientOpenIso φ j M).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [h, Iso.hom_inv_id_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the objectwise proper/open etale coefficient map on the stated input
class. All other constituent maps are already natural transformations or composites of
them; the site formulas are their conjugates on the full bounded-below subcategory.
Source: blueprint final sentence and Step 11
(blueprint: lem-sp-et-proet-coefficient-compatibility).

Proof: the proper coefficient comparison is a natural counit mate. Invert the open
coefficient map and transpose under the open adjunction: naturality becomes naturality
of its unit and of scalar/pullback comparison. Transpose back and compose with the proper
mate. This gives the displayed equation. Naturality of c, delta, canonical compactification
changes and compositors then gives naturality of every square and every transported
counit identity, as asserted in Step 11. -/
theorem etaleProEtaleCoefficientCompatibility_naturality
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (ell p : ℕ) [Fact ell.Prime] (_hp : 0 < p) (_hEll : p ≠ ell)
    (k : Type u) [Field k] [CharP k p]
    (_hA : ∃ n : ℕ, ∀ x : A, (ell ^ n) • x = 0)
    (_hB : ∃ n : ℕ, ∀ x : B, (ell ^ n) • x = 0) (φ : A →+* B)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (L M : Etale.DerivedCategoryModule A X)
    (_hL : AdjunctionTransfer.etaleProperty A X L)
    (_hM : AdjunctionTransfer.etaleProperty A X M) (a : L ⟶ M) :
    (Etale.scalarExtension φ Y).map
        ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map a) ≫
      etaleCoefficientMap φ c M =
    etaleCoefficientMap φ c L ≫
      (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).map
        ((Etale.scalarExtension φ X).map a) := by
  unfold etaleCoefficientMap
  have h := (Etale.scalarMate φ c.g).naturality
    ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.map a)
  dsimp only [Functor.comp_map] at h
  change (Etale.scalarExtension φ Y).map
      ((Etale.lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctor.map
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.map a)) ≫
      (Etale.scalarMate φ c.g).app
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj M) ≫
      (Etale.lowerStar (ModuleCat.{u + 1} B) c.g).rightDerivedFunctor.map
        (Etale.properOpenCoefficientOpenIso φ c.i M).hom =
    ((Etale.scalarMate φ c.g).app
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj L) ≫
      (Etale.lowerStar (ModuleCat.{u + 1} B) c.g).rightDerivedFunctor.map
        (Etale.properOpenCoefficientOpenIso φ c.i L).hom) ≫
      (Etale.lowerStar (ModuleCat.{u + 1} B) c.g).rightDerivedFunctor.map
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} B) c.i).mapDerivedCategory.map
          ((Etale.scalarExtension φ X).map a))
  rw [← Category.assoc, h, Category.assoc, ← Functor.map_comp,
    openCoefficientHom_naturality φ c.i a, Functor.map_comp, Category.assoc]

end AlgebraicGeometry.ProEtale.CoefficientCompatibility
