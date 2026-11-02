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
public import WeilConjectures.AlgebraicGeometry.FixedComparisonDirectImageMate
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
import WeilConjectures.AlgebraicGeometry.FixedComparisonDirectImageMate
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

end AlgebraicGeometry.ProEtale.CoefficientCompatibility
