/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImage
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedComparisonDirectImageMate
public import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZeroComparison
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.AlgebraicGeometry.AdjunctionTransfer.EtaleProEtaleAdjunctionTransfer
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportComparisons
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalization
public import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FiniteEtale
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalCompactSupportSiteComparison
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.WitnessCompatibility
public import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleScalarMateProjection
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientRefinement
import WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.EtaleProEtaleCompactScalarSquare
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImage
import WeilConjectures.AlgebraicGeometry.Fixed.FixedComparisonDirectImageMate
import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZeroComparison
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.Noetherian.Defs
import WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible
import WeilConjectures.CategoryTheory.Ringed.RingedProEtaleTorAmplitudeOfUniverses
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Limits.Final
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.WitnessCompatibility
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
import WeilConjectures.AlgebraicGeometry.Etale.Sum.EtaleSumScalarRepresentative
import WeilConjectures.AlgebraicGeometry.Etale.EtaleFlatConstructibleModel
import all WeilConjectures.AlgebraicGeometry.Etale.EtaleCompactificationBoundedModels
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
import WeilConjectures.AlgebraicGeometry.EtaleCompactSupportGraphSheafNormalization
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalizationDataSupplement
import WeilConjectures.SixFunctors.BaseChange.Etale
import WeilConjectures.ConstructibleSheaf.EtaleMorphismDescent
public import WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.EtaleProEtaleCoefficientTransport
public import WeilConjectures.AlgebraicGeometry.Finite.Compact.FiniteCompactSupportDomains
public import WeilConjectures.SmoothPurity.EtaleCompactSupportGraphSheafNormalization

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
  have hLB : DerivedCategory.TStructure.t.plus
      ((Etale.scalarExtension ψ X).obj L.obj) := by
    first
    | exact (hdom.2.2.1 ⟨X, (Etale.scalarExtension ψ X).obj L.obj⟩
        List.mem_cons_self).1.2.2.2
    | exact (hdom.2.1 ⟨X, (Etale.scalarExtension ψ X).obj L.obj⟩ (by simp)).2.2.2.1
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
    first
    | exact
        let hFA := hdom.1
        let hFAB := (hdom.2.2.1
          ⟨Y, (Etale.scalarExtension ψ Y).obj
            ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} RA) c).obj
              L.obj)⟩ (List.mem_cons_of_mem _ List.mem_cons_self)).1
        let hFB := (hdom.2.2.1
          ⟨Y, (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} RB) c).obj
            ((Etale.scalarExtension ψ X).obj L.obj)⟩
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))).1
        ⟨hFA.2.2.2, hFAB.2.2.2, hFB.2.2.2,
          etaleProperty_of_domain RA Y _ hFA.1 hFA.2.1 hFA.2.2.1⟩
    | have hFA := hdom.1
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

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 2048 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 2048 in
set_option backward.isDefEq.respectTransparency false in
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

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
end AlgebraicGeometry.ProEtale.CoefficientCompatibility
