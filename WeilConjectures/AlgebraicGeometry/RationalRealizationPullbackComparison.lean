/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RationalModuleRealizationFunctor
public import WeilConjectures.AlgebraicGeometry.PbcQbarCompletedPullback
public import WeilConjectures.CategoryTheory.LocalizationInverseImageCoherence
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedPullbackComposition
public import WeilConjectures.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleRingInverseImage
public import WeilConjectures.AlgebraicGeometry.ProfiniteCoefficientInverseImageSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.AlgebraicGeometry.ProEtaleOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Mathlib.CategoryTheory.Types.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.Vanishing
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
public import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
public import Mathlib.CategoryTheory.Sites.Pullback
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
public import WeilConjectures.CategoryTheory.SitePullbackAbelianUnderlyingSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleAlgebraicInverseImage
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import WeilConjectures.CategoryTheory.SiteInverseImageTensor
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImageTensorComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleTensorCompositionUnit
public import WeilConjectures.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import all WeilConjectures.AlgebraicGeometry.ExtensionZeroPerfectModelTransport
import WeilConjectures.AlgebraicGeometry.OrdinaryIntegralLocalModels
import WeilConjectures.AlgebraicGeometry.PbcUniformCompleteTriangulated
import WeilConjectures.AlgebraicGeometry.PbcRationalTransport
import WeilConjectures.CategoryTheory.ScalarLocalizationNaturalIso
import WeilConjectures.AlgebraicGeometry.RationalScalarBalancedLocalization
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientGeneralPullbackIso
import all WeilConjectures.AlgebraicGeometry.ProEtaleOperationsSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedPullbackComposition
import all WeilConjectures.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtaleRingInverseImage
import all WeilConjectures.AlgebraicGeometry.ProfiniteCoefficientInverseImageSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Adjunction.Mates
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import all Mathlib.CategoryTheory.Sites.Pullback
import all WeilConjectures.CategoryTheory.SiteCoveringAxioms
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import all Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import all WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import all WeilConjectures.CategoryTheory.SitePullbackAbelianUnderlyingSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtaleAlgebraicInverseImage
import all WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import all WeilConjectures.CategoryTheory.SiteInverseImageTensor
import all WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Mathlib.CategoryTheory.Monoidal.Ring
import all WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all WeilConjectures.AlgebraicGeometry.ProEtaleInverseImageTensorComparisonSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtaleTensorCompositionUnit
import all WeilConjectures.AlgebraicGeometry.ProEtaleConstantRingOperations
import all Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import all WeilConjectures.AlgebraicGeometry.CompletedTowerPullbackSupplement
import all WeilConjectures.AlgebraicGeometry.PbcScalarRestriction

/-!
# Rational realization of the specified completed-pullback unit

Source: Bhatt--Scholze, Proposition 6.6.11, Lemma 6.5.9 and Remark 6.8.15,
pp. 50, 54, 62 (blueprint: lem-per-rational-realization-pullback-comparison).

The integral unit is the published strict quotient-tower unit. The ordinary
comparison is fixed on tensor generators and by its derived computation counits.
Its descent retains all raw fraction arrows, without taking a Karoubi envelope.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The scalar-localization map specified by the recorded realization data.
Source: Bhatt--Scholze, Lemma 6.8.2 and Remark 6.8.15
(blueprint: lem-per-rational-realization-pullback-comparison). -/
abbrev rationalPullScalar {T : Scheme.{u}} [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (s : RationalModuleRealization l E T) := s.integralIso.hom ≫ s.inclusion

/-- An actual raw fraction with integral numerator and the given uniformizer power.
Source: Bhatt--Scholze, Section 6.8, scalar localization
(blueprint: lem-per-rational-realization-pullback-comparison). -/
def rationalPullFraction (T : Scheme.{u})
    {K L : PbcBoundedConstructibleComplete T (pbcIntegralDatum l E)}
    (f : K ⟶ L) (n : ℕ) :
    (pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K ⟶
      (pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E)).obj L :=
  (IsLocalization.Away.invSelf (S := Localization.Away (pbcUniformizer l E))
    (pbcUniformizer l E)) ^ n •
      (pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E)).map f

/-- Ordinary rational ringed pullback with its actual coefficient map, without an
isomorphism assumption on that map. Source: Bhatt--Scholze, Remark 6.8.15
(blueprint: lem-per-rational-realization-pullback-comparison). -/
abbrev rationalPullModule {S T : Scheme.{u}} (g : S ⟶ T)
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
      (rationalCoefficientSheaf l T E) ⟶ rationalCoefficientSheaf l S E) :=
  proEtaleRingModulePullback g (rationalCoefficientSheaf l T E)
      ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
        (rationalCoefficientSheaf l T E)) (Iso.refl _) ⋙ pbcExtend c

/-- Unbounded derived rational ringed pullback: exact inverse image followed by
actual derived scalar extension. Source: Bhatt--Scholze, Remark 6.8.15
(blueprint: lem-per-rational-realization-pullback-comparison). -/
def rationalPullDerived {S T : Scheme.{u}} (g : S ⟶ T)
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
      (rationalCoefficientSheaf l T E) ⟶ rationalCoefficientSheaf l S E) :=
  adicTowerPullback g (rationalCoefficientSheaf l T E) ⋙ pbcDerivedExtend c

/-- The ordinary computation counit of that composite on cochain representatives.
Source: Stacks Tag 06YY; Bhatt--Scholze, Remark 6.8.15
(blueprint: lem-per-rational-realization-pullback-comparison). -/
def rationalPullComplexCounit {S T : Scheme.{u}} (g : S ⟶ T)
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
      (rationalCoefficientSheaf l T E) ⟶ rationalCoefficientSheaf l S E)
    (P : CochainComplex (pbcModules T (rationalCoefficientSheaf l T E)) ℤ) :
    (rationalPullDerived l E g c).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        (((rationalPullModule l E g c).mapHomologicalComplex (.up ℤ)).obj P) :=
  (pbcDerivedExtend c).map
      ((proEtaleRingDerivedPullbackFactors g (rationalCoefficientSheaf l T E)
        ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
          (rationalCoefficientSheaf l T E)) (Iso.refl _)).hom.app P) ≫
    pbcComplexCounit c
      (((proEtaleRingModulePullback g (rationalCoefficientSheaf l T E)
        ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
          (rationalCoefficientSheaf l T E)) (Iso.refl _)).mapHomologicalComplex (.up ℤ)).obj P)

variable {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
  [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]

/-- Integral preservation and invertibility of exactly the quotient-tower unit.
Membership includes intrinsic completeness, uniform reductions and compatible etale origins.
Source: Bhatt--Scholze, Proposition 6.6.11 and Lemma 6.5.9
(blueprint: lem-per-rational-realization-pullback-comparison). -/
structure RationalPullIntegral (g : X ⟶ Y) where
  /-- Ordinary coefficient pullback remains in the full integral category. -/
  ordinary_mem : ∀ K : PbcBoundedConstructibleComplete Y (pbcIntegralDatum l E),
    PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)
      ((pbcActualDerivedPull g (pbcIntegralDatum l E)).obj K.obj)
  /-- The completed object belongs to that same category. -/
  completed_mem : ∀ K : PbcBoundedConstructibleComplete Y (pbcIntegralDatum l E),
    PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)
      ((pbcActualStrictCompletedPull (pbcIntegralDatum l E) g).obj K.obj)
  /-- This is the published unit, with its strict quotient augmentation. -/
  unit_isIso : ∀ K : PbcBoundedConstructibleComplete Y (pbcIntegralDatum l E),
    IsIso ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) g).app K.obj)

/-- Restriction keeps the actual strict completed-pullback objects and arrows.
Source: Bhatt--Scholze, Lemma 6.5.9 and Remark 6.8.15
(blueprint: lem-per-rational-realization-pullback-comparison). -/
def RationalPullIntegral.completedFunctor {g : X ⟶ Y} (a : RationalPullIntegral l E g) :=
  pbcConditionalIntegral (pbcIntegralDatum l E)
    (pbcActualStrictCompletedPull (pbcIntegralDatum l E) g) a.completed_mem

/-- All maps of the comparison, with their tensor, derived and fraction normalizations.
The coefficient map is fixed by its localization unit, without an isomorphism hypothesis.
Source: Bhatt--Scholze, Proposition 6.6.11 and Remark 6.8.15
(blueprint: lem-per-rational-realization-pullback-comparison). -/
structure RationalRealizationPullbackComparison (g : X ⟶ Y)
    (sX : RationalModuleRealization l E X) (sY : RationalModuleRealization l E Y) where
  /-- The integral preservation and specified-unit assertions. -/
  integral : RationalPullIntegral l E g
  /-- Localization of the canonical integral coefficient map. -/
  rationalCoefficient : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
    (rationalCoefficientSheaf l Y E) ⟶ rationalCoefficientSheaf l X E
  /-- The ring comparison preserves each inverse-image numerator. -/
  rational_normalization : rationalCoefficientRestrictionNormalized l E g
    rationalCoefficient
  /-- This square fixes the localized coefficient map on its localization unit. -/
  coefficient_square : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
      (rationalPullScalar l E sY) ≫ rationalCoefficient =
    completedCoefficientMap g (pbcIntegralDatum l E) ≫ rationalPullScalar l E sX
  /-- Balanced flattening between the two ordinary module expressions. -/
  moduleComparison : pbcActualModulePull g (pbcIntegralDatum l E) ⋙
      pbcExtend (rationalPullScalar l E sX) ≅
    pbcExtend (rationalPullScalar l E sY) ⋙
      rationalPullModule l E g rationalCoefficient
  /-- On generators this inserts the same numerator and tensor units on either side.
  Linearity determines the balanced tensor maps, including all denominators. -/
  module_unit : ∀ (M : pbcModules Y (pbcAdicCompletion Y (pbcIntegralDatum l E)))
      (V : Y.ProEt) (m : M.val.obj (op V)),
    (moduleComparison.hom.app M).val.app (op ((proEtaleBaseChange g).obj V))
      (pbcTensorSection (rationalPullScalar l E sX)
        ((pbcActualModulePull g (pbcIntegralDatum l E)).obj M)
        (op ((proEtaleBaseChange g).obj V)) 1
        (pbcActualModuleUnitSection g (pbcIntegralDatum l E) M V m)) =
    pbcTensorSection rationalCoefficient
      ((proEtaleRingModulePullback g (rationalCoefficientSheaf l Y E)
        ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
          (rationalCoefficientSheaf l Y E)) (Iso.refl _)).obj
            ((pbcExtend (rationalPullScalar l E sY)).obj M))
      (op ((proEtaleBaseChange g).obj V)) 1
      (proEtaleRingModuleUnitSection g (rationalCoefficientSheaf l Y E)
        ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
          (rationalCoefficientSheaf l Y E)) (Iso.refl _)
        ((pbcExtend (rationalPullScalar l E sY)).obj M) V
        (pbcTensorSection (rationalPullScalar l E sY) M (op V) 1 m))
  /-- The ordinary comparison in the unbounded derived categories. -/
  ordinaryComparison : pbcActualDerivedPull g (pbcIntegralDatum l E) ⋙
      pbcDerivedExtend (rationalPullScalar l E sX) ≅
    pbcDerivedExtend (rationalPullScalar l E sY) ⋙
      rationalPullDerived l E g rationalCoefficient
  /-- The derived arrow is the localization of the balanced termwise arrow.
  On flat-term K-flat representatives the computation counits are invertible. -/
  derived_normalization : ∀ P : CochainComplex
      (pbcModules Y (pbcAdicCompletion Y (pbcIntegralDatum l E))) ℤ,
    ordinaryComparison.hom.app (DerivedCategory.Q.obj P) ≫
        (rationalPullDerived l E g rationalCoefficient).map
            (pbcComplexCounit (rationalPullScalar l E sY) P) ≫
        rationalPullComplexCounit l E g rationalCoefficient
            (((pbcExtend (rationalPullScalar l E sY)).mapHomologicalComplex (.up ℤ)).obj P) =
      (pbcDerivedExtend (rationalPullScalar l E sX)).map
          (pbcActualPullComplexCounit g (pbcIntegralDatum l E) P) ≫
        pbcComplexCounit (rationalPullScalar l E sX)
          (((pbcActualModulePull g (pbcIntegralDatum l E)).mapHomologicalComplex
            (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex moduleComparison (.up ℤ)).hom.app P)
  /-- Completed pullback on the raw rationalizations. -/
  rawPull : PbcRationalCategory Y (pbcIntegralDatum l E) (pbcUniformizer l E) ⥤
    PbcRationalCategory X (pbcIntegralDatum l E) (pbcUniformizer l E)
  /-- No objects are added to raw localization. -/
  raw_objects : ∀ K : PbcBoundedConstructibleComplete Y (pbcIntegralDatum l E),
    rawPull.obj ((pbcRationalization Y (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K) =
      (pbcRationalization X (pbcIntegralDatum l E) (pbcUniformizer l E)).obj
        ((integral.completedFunctor l E).obj K)
  /-- Every fraction keeps its denominator and applies the actual pullback to its numerator. -/
  raw_fractions : ∀ (K L : PbcBoundedConstructibleComplete Y (pbcIntegralDatum l E))
      (f : K ⟶ L) (n : ℕ),
    rawPull.map (rationalPullFraction l E Y f n) = eqToHom (raw_objects K) ≫
      rationalPullFraction l E X ((integral.completedFunctor l E).map f) n ≫
        eqToHom (raw_objects L).symm
  /-- The required natural isomorphism on all raw rational morphisms. -/
  alpha : rawPull ⋙ sX.J ≅ sY.J ⋙
    rationalPullDerived l E g rationalCoefficient
  /-- Equivalently, alpha is F of the inverse specified unit followed by flattening.
  Object equalities are only the recorded formulas J(QK)=F(K) and raw_objects. -/
  alpha_normalization : ∀ K : PbcBoundedConstructibleComplete Y (pbcIntegralDatum l E),
    (pbcDerivedExtend (rationalPullScalar l E sX)).map
        ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) g).app K.obj) ≫
      eqToHom (sX.objects ((integral.completedFunctor l E).obj K)).symm ≫
      sX.J.map (eqToHom (raw_objects K).symm) ≫ alpha.hom.app
        ((pbcRationalization Y (pbcIntegralDatum l E) (pbcUniformizer l E)).obj K) ≫
      (rationalPullDerived l E g rationalCoefficient).map
          (eqToHom (sY.objects K)) = ordinaryComparison.hom.app K.obj

/-- Ordinary pullback takes each perfect constant model to the same perfect scalar model.
This applies on pulled-back strata and their pro-etale covering charts, without imposing
noetherianity on a chart. Source: Bhatt--Scholze, Proposition 6.6.11 and Remark 6.8.15
(blueprint: lem-per-rational-realization-pullback-comparison).

Proof: represent P by a bounded complex of finite projective A-modules. Its completed
constant realization has flat terms and is K-flat. The ordinary pullback computation
counit therefore is invertible. Termwise balanced tensor flattening sends
b tensor (a tensor p) to b c(a) tensor p, with inverse inserting one. These maps commute
with differentials and the finite-projective idempotents, as in
lem-tw-ordinary-pullback-stratified-models. Localizing gives the asserted model. -/
theorem rationalRealizationPullbackModel {S T : Scheme.{u}} (h : S ⟶ T)
    (P : completedConstantDerived (ModuleCat.{u + 1} (PbcIntegralRing l E)))
    (_hP : @DerivedCategory.IsPerfectRingComplex (PbcIntegralRing l E) _
      (HasDerivedCategory.standard (ModuleCat.{u + 1} (PbcIntegralRing l E))) P) :
    Nonempty ((pbcActualDerivedPull h (pbcIntegralDatum l E)).obj
        ((integralConstantDerived T (pbcIntegralDatum l E)).obj P) ≅
      (integralConstantDerived S (pbcIntegralDatum l E)).obj P) := by
  exact ⟨((cbcDatumOrdinaryTransport (pbcIntegralDatum l E) h).app
    ((integralConstantDerived T (pbcIntegralDatum l E)).obj P)) ≪≫
      (integralConstantDerivedPullIso (pbcIntegralDatum l E) h).app P⟩

omit [Fact l.Prime] in
private theorem rationalPullPrimeUnit (T : Scheme.{u})
    [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))] : IsUnit (l : Γ(T, ⊤)) := by
  apply T.toRingedSpace.isUnit_of_isUnit_germ
  intro x hx
  simpa only [map_natCast] using
    (Fact.out : ∀ t : T, IsUnit (l : T.presheaf.stalk t)) x

private theorem rationalPullOrdinaryMem (g : X ⟶ Y)
    (K : PbcBoundedConstructibleComplete Y (pbcIntegralDatum l E)) :
    PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)
      ((pbcActualDerivedPull g (pbcIntegralDatum l E)).obj K.obj) := by
  let d := pbcIntegralDatum l E
  have hK := (integralStratifiedPerfectCharacterization Y l E Fact.out
    (rationalPullPrimeUnit l Y) K.obj).1.mp K.property
  have hP := integralStratifiedPerfect_pullback d g K.obj hK
  have h := (integralStratifiedPerfectCharacterization X l E Fact.out
    (rationalPullPrimeUnit l X) _).1.mpr hP
  let := (pbcIntegralUniformComplete_isTriangulated l E X Fact.out Fact.out).1
  exact ObjectProperty.prop_of_iso _
    ((cbcDatumOrdinaryTransport d g).app K.obj).symm h

private theorem rationalPullIntegralData (g : X ⟶ Y) : RationalPullIntegral l E g := by
  let d := pbcIntegralDatum l E
  have hmem := rationalPullOrdinaryMem l E g
  have hu (K : PbcBoundedConstructibleComplete Y d) :
      IsIso ((pbcActualCompletedPullUnit g d).app K.obj) := by
    exact (Adjunction.ofIsRightAdjoint
      (ObjectProperty.ι (PbcIsIntrinsicallyComplete X d))).isIso_unit_app_iff_mem_essImage.mpr
        ⟨⟨_, (hmem K).1⟩, ⟨Iso.refl _⟩⟩
  obtain ⟨e, he, _⟩ := pbcActualCompletedPullback_tower d g
  have hs (K : PbcBoundedConstructibleComplete Y d) :
      IsIso ((pbcActualStrictCompletedPullUnit d g).app K.obj) := by
    let M : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete Y d) :=
      ⟨K.obj, K.property.1⟩
    have : IsIso ((pbcActualStrictCompletedPullUnit d g).app K.obj ≫ e.hom.app M) := by
      rw [he M]
      exact hu K
    exact IsIso.of_isIso_comp_right _ (e.hom.app M)
  let := (pbcIntegralUniformComplete_isTriangulated l E X Fact.out Fact.out).1
  refine { ordinary_mem := hmem, unit_isIso := hs, completed_mem := ?_ }
  intro K
  have := hs K
  exact ObjectProperty.prop_of_iso _
    (asIso ((pbcActualStrictCompletedPullUnit d g).app K.obj)) (hmem K)

private theorem rationalPullInclusion {T : Scheme.{u}} [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (s : RationalModuleRealization l E T) :
    s.inclusion = integralRationalCoefficientMap l E T := by
  let := coefficientExtensionNormedField l E
  apply Sheaf.hom_ext
  ext V a
  apply ContinuousMap.ext
  intro x
  apply ULift.down_injective
  exact (s.inclusion_normalization V.unop a x).trans
    ((integralRationalCoefficientMap_normalized l E T) V.unop a x).symm

private theorem rationalPullCoefficientSquare (g : X ⟶ Y)
    (sX : RationalModuleRealization l E X) (sY : RationalModuleRealization l E Y) :
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
        (rationalPullScalar l E sY) ≫ rationalContinuousPullback l E g =
      completedCoefficientMap g (pbcIntegralDatum l E) ≫ rationalPullScalar l E sX := by
  let L := proEtaleSheafInverseImage g CommRingCat.{u + 1}
  have hn := rationalBalancedGeometricNormalization l E g sY sX
  change L.map sY.integralIso.inv ≫
    completedCoefficientMap g (pbcIntegralDatum l E) ≫ sX.integralIso.hom =
      integralContinuousPullback l E g at hn
  have hi : completedCoefficientMap g (pbcIntegralDatum l E) ≫ sX.integralIso.hom =
      L.map sY.integralIso.hom ≫ integralContinuousPullback l E g := by
    apply (cancel_epi (L.map sY.integralIso.inv)).1
    simpa only [← Category.assoc, ← L.map_comp, Iso.inv_hom_id, L.map_id,
      Category.id_comp] using hn
  change L.map (sY.integralIso.hom ≫ sY.inclusion) ≫ _ =
    completedCoefficientMap g (pbcIntegralDatum l E) ≫ sX.integralIso.hom ≫ sX.inclusion
  rw [rationalPullInclusion l E sX, rationalPullInclusion l E sY,
    L.map_comp, Category.assoc, ← integralContinuousPullback_inclusion l E g,
    ← Category.assoc, ← hi, Category.assoc]

private theorem rationalPullAdjointSquare
    {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (a : L ⊣ R) {A B : C} {A' B' : D} (α : A ⟶ B) (β : A' ⟶ B')
    (cI : L.obj A ⟶ A') (c : L.obj B ⟶ B') (h : L.map α ≫ c = cI ≫ β) :
    α ≫ a.unit.app B ≫ R.map c = (a.unit.app A ≫ R.map cI) ≫ R.map β := by
  calc
    _ = (a.unit.app A ≫ R.map (L.map α)) ≫ R.map c := by
      simpa only [Functor.id_map, Functor.comp_map, Category.assoc] using
        congrArg (fun q ↦ q ≫ R.map c) (a.unit.naturality α)
    _ = a.unit.app A ≫ R.map (L.map α ≫ c) := by rw [R.map_comp, Category.assoc]
    _ = _ := by rw [h, R.map_comp, Category.assoc]

set_option maxHeartbeats 2000000 in
-- Comparing the nested restrictions unfolds the concrete sheaf module presentations.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private def rationalPullRightIso (g : X ⟶ Y)
    (sX : RationalModuleRealization l E X) (sY : RationalModuleRealization l E Y) :
    pbcRestrict (rationalContinuousPullback l E g) ⋙
        proEtaleRingModuleDirectImage g (rationalCoefficientSheaf l Y E)
          ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
            (rationalCoefficientSheaf l Y E)) (Iso.refl _) ⋙
        pbcRestrict (rationalPullScalar l E sY) ≅
      pbcRestrict (rationalPullScalar l E sX) ⋙
        pbcActualModulePush g (pbcIntegralDatum l E) := by
  let L := proEtaleSheafInverseImage g CommRingCat.{u + 1}
  let R := proEtaleSheafDirectImage g CommRingCat.{u + 1}
  let a := proEtaleSheafAdjunction g CommRingCat.{u + 1}
  have h := rationalPullAdjointSquare a
    (rationalPullScalar l E sY) (rationalPullScalar l E sX)
    (completedCoefficientMap g (pbcIntegralDatum l E)) (rationalContinuousPullback l E g)
    (rationalPullCoefficientSquare l E g sX sY)
  have h' : rationalPullScalar l E sY ≫
      proEtaleRingDirectImageMap g (rationalCoefficientSheaf l Y E)
        (L.obj (rationalCoefficientSheaf l Y E)) (Iso.refl _) ≫
        R.map (rationalContinuousPullback l E g) =
      completedCoefficientDirectImageMap g (pbcIntegralDatum l E) ≫
        R.map (rationalPullScalar l E sX) := by
    dsimp only [proEtaleRingDirectImageMap, Iso.refl_hom]
    erw [(proEtaleSheafDirectImage g CommRingCat.{u + 1}).map_id, Category.comp_id]
    simpa only [a, L, R, completedCoefficientDirectImageMap, Category.assoc] using h
  let ay := (adicLisseForget Y).map (rationalPullScalar l E sY)
  let ax := (adicLisseForget X).map (rationalPullScalar l E sX)
  let aq := (adicLisseForget Y).map
    (proEtaleRingDirectImageMap g (rationalCoefficientSheaf l Y E)
      (L.obj (rationalCoefficientSheaf l Y E)) (Iso.refl _))
  let cc := (adicLisseForget X).map (rationalContinuousPullback l E g)
  let ar := pbcActualStructureMap g (pbcIntegralDatum l E)
  have hh : ay ≫ aq ≫ (proEtaleSheafDirectImage g RingCat.{u + 1}).map cc =
      ar ≫ (proEtaleSheafDirectImage g RingCat.{u + 1}).map ax :=
    congrArg (fun q ↦ (adicLisseForget Y).map q) h'
  exact SheafOfModules.pushforwardCongr (F := proEtaleBaseChange g)
    (J := ProEt.topology Y) (K := ProEt.topology X)
    (R := (adicLisseForget X).obj (rationalCoefficientSheaf l X E))
    (S := (adicLisseForget Y).obj (pbcAdicCompletion Y (pbcIntegralDatum l E)))
    (φ := ay ≫ aq ≫ (proEtaleSheafDirectImage g RingCat.{u + 1}).map cc)
    (ψ := ar ≫ (proEtaleSheafDirectImage g RingCat.{u + 1}).map ax) hh

private theorem rationalPullRightIso_sections (g : X ⟶ Y)
    (sX : RationalModuleRealization l E X) (sY : RationalModuleRealization l E Y)
    (N : pbcModules X (rationalCoefficientSheaf l X E)) (U : Y.ProEtᵒᵖ)
    (x : N.val.obj ((proEtaleBaseChange g).op.obj U)) :
    ((rationalPullRightIso l E g sX sY).hom.app N).val.app U x = x := by
  rfl

private theorem rationalPullModuleComparison (g : X ⟶ Y)
    (sX : RationalModuleRealization l E X) (sY : RationalModuleRealization l E Y) :
    ∃ e : pbcActualModulePull g (pbcIntegralDatum l E) ⋙
        pbcExtend (rationalPullScalar l E sX) ≅
      pbcExtend (rationalPullScalar l E sY) ⋙
        rationalPullModule l E g (rationalContinuousPullback l E g),
      ∀ (M : pbcModules Y (pbcAdicCompletion Y (pbcIntegralDatum l E)))
        (V : Y.ProEt) (m : M.val.obj (op V)),
      (e.hom.app M).val.app (op ((proEtaleBaseChange g).obj V))
        (pbcTensorSection (rationalPullScalar l E sX)
          ((pbcActualModulePull g (pbcIntegralDatum l E)).obj M)
          (op ((proEtaleBaseChange g).obj V)) 1
          (pbcActualModuleUnitSection g (pbcIntegralDatum l E) M V m)) =
      pbcTensorSection (rationalContinuousPullback l E g)
        ((proEtaleRingModulePullback g (rationalCoefficientSheaf l Y E)
          ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
            (rationalCoefficientSheaf l Y E)) (Iso.refl _)).obj
              ((pbcExtend (rationalPullScalar l E sY)).obj M))
        (op ((proEtaleBaseChange g).obj V)) 1
        (proEtaleRingModuleUnitSection g (rationalCoefficientSheaf l Y E)
          ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
            (rationalCoefficientSheaf l Y E)) (Iso.refl _)
          ((pbcExtend (rationalPullScalar l E sY)).obj M) V
          (pbcTensorSection (rationalPullScalar l E sY) M (op V) 1 m)) := by
  let a := (pbcActualModuleAdjunction g (pbcIntegralDatum l E)).comp
    (pbcScalarAdjunction (rationalPullScalar l E sX))
  let b := (pbcScalarAdjunction (rationalPullScalar l E sY)).comp
    ((proEtaleRingModuleAdjunction g (rationalCoefficientSheaf l Y E)
      ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
        (rationalCoefficientSheaf l Y E)) (Iso.refl _)).comp
      (pbcScalarAdjunction (rationalContinuousPullback l E g)))
  let d := rationalPullRightIso l E g sX sY
  let e := (conjugateIsoEquiv b a).symm d
  refine ⟨e, ?_⟩
  intro M V m
  have h := congrArg (fun q ↦ q.val.app (op V) m)
    (unit_conjugateEquiv_symm b a d.hom M).symm
  change (e.hom.app M).val.app (op ((proEtaleBaseChange g).obj V))
      (((pbcScalarAdjunction (rationalPullScalar l E sX)).unit.app _).val.app
        (op ((proEtaleBaseChange g).obj V))
        (((pbcActualModuleAdjunction g (pbcIntegralDatum l E)).unit.app M).val.app
          (op V) m)) =
    (d.hom.app _).val.app (op V)
      (((pbcScalarAdjunction (rationalContinuousPullback l E g)).unit.app _).val.app
        (op ((proEtaleBaseChange g).obj V))
        (((proEtaleRingModuleAdjunction g (rationalCoefficientSheaf l Y E)
          ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
            (rationalCoefficientSheaf l Y E)) (Iso.refl _)).unit.app _).val.app
          (op V)
          (((pbcScalarAdjunction (rationalPullScalar l E sY)).unit.app M).val.app
            (op V) m))) at h
  have hn := canonicalAdjunction_normalized g (rationalCoefficientSheaf l Y E)
    ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
      (rationalCoefficientSheaf l Y E)) (Iso.refl _)
  dsimp only [proEtaleRingModuleAdjunctionNormalized] at hn
  simp only [d, rationalPullRightIso_sections, pbcScalarAdjunction,
    (pbcScalarAdjunction_exists _).exists.choose_spec,
    pbcActualModuleAdjunction, (pbcActualModuleAdjunction_exists _ _).exists.choose_spec,
    hn] at h
  convert h using 1
  rfl

private theorem rationalPullDescendIso
    {C D : Type*} [Category C] [Abelian C] [HasDerivedCategory C] [Category D]
    (F G : DerivedCategory C ⥤ D) (U V : CochainComplex C ℤ ⥤ D)
    (a : DerivedCategory.Q ⋙ F ≅ U) (b : DerivedCategory.Q ⋙ G ≅ V) (e : U ≅ V) :
    ∃ d : F ≅ G, ∀ P : CochainComplex C ℤ,
      d.hom.app (DerivedCategory.Q.obj P) ≫ b.hom.app P =
        a.hom.app P ≫ e.hom.app P := by
  let ff := Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ)) D
  let e₀ := a ≪≫ e ≪≫ b.symm
  let d := ff.preimageIso e₀
  have hd (P : CochainComplex C ℤ) :
      d.hom.app (DerivedCategory.Q.obj P) = e₀.hom.app P :=
    congrArg (fun q ↦ q.app P) (ff.map_preimage e₀.hom)
  refine ⟨d, fun P ↦ ?_⟩
  rw [hd]
  simp only [e₀, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id]

private def rationalPullCounit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] (L : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ L ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) :
    DerivedCategory.Q ⋙ L ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  whiskerRight (DerivedCategory.quotientCompQhIso C).inv L ≫
    whiskerLeft (HomotopyCategory.quotient C (.up ℤ)) ε ≫
    whiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)).hom DerivedCategory.Qh ≫
    whiskerLeft (F.mapHomologicalComplex (.up ℤ)) (DerivedCategory.quotientCompQhIso D).hom

private def rationalPullScalarFactors {T : Scheme.{u}}
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    [PreservesFiniteLimits (pbcExtend φ)] [PreservesFiniteColimits (pbcExtend φ)] :
    DerivedCategory.Q ⋙ pbcDerivedExtend φ ≅
      (pbcExtend φ).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q := by
  have := pbcDerivedExtension_universal φ
  have : IsIso (pbcExtensionCounit φ) :=
    exactPullbackCounit_isIso (pbcExtend φ) (pbcDerivedExtend φ) (pbcExtensionCounit φ)
  let ε := rationalPullCounit (pbcExtend φ) (pbcDerivedExtend φ) (pbcExtensionCounit φ)
  have : IsIso ε := by dsimp only [ε, rationalPullCounit]; infer_instance
  exact asIso ε

private def rationalPullOrdinaryFactors (g : X ⟶ Y) :
    DerivedCategory.Q ⋙ pbcActualDerivedPull g (pbcIntegralDatum l E) ≅
      (pbcActualModulePull g (pbcIntegralDatum l E)).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q := by
  have := completedModulePullback_finiteLimits g (pbcIntegralDatum l E)
  have := completedModulePullback_finiteColimits g (pbcIntegralDatum l E)
  have : IsIso (pbcActualPullCounit g (pbcIntegralDatum l E)) :=
    exactPullbackCounit_isIso (pbcActualModulePull g (pbcIntegralDatum l E))
      (pbcActualDerivedPull g (pbcIntegralDatum l E))
      (pbcActualPullCounit g (pbcIntegralDatum l E))
  let ε := rationalPullCounit (pbcActualModulePull g (pbcIntegralDatum l E))
    (pbcActualDerivedPull g (pbcIntegralDatum l E)) (pbcActualPullCounit g (pbcIntegralDatum l E))
  have : IsIso ε := by dsimp only [ε, rationalPullCounit]; infer_instance
  exact asIso ε

private theorem rationalPullScalarFactors_app {T : Scheme.{u}}
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    [PreservesFiniteLimits (pbcExtend φ)] [PreservesFiniteColimits (pbcExtend φ)]
    (P : CochainComplex (pbcModules T R) ℤ) :
    (rationalPullScalarFactors φ).hom.app P = pbcComplexCounit φ P := by
  rfl

omit [IsNoetherian X] [IsNoetherian Y]
  [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))] in
private theorem rationalPullOrdinaryFactors_app (g : X ⟶ Y)
    (P : CochainComplex (pbcModules Y (pbcAdicCompletion Y (pbcIntegralDatum l E))) ℤ) :
    (rationalPullOrdinaryFactors l E g).hom.app P =
      pbcActualPullComplexCounit g (pbcIntegralDatum l E) P := by
  rfl

private theorem rationalPullExtendExact {T : Scheme.{u}}
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (c : R ⟶ S) [IsIso c] :
    PreservesFiniteLimits (pbcExtend c) ∧ PreservesFiniteColimits (pbcExtend c) := by
  let e := proEtaleScalarEquivalence T
    ((sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso (asIso c))
  have : (pbcRestrict c).IsEquivalence := e.isEquivalence_functor
  have : (pbcExtend c).IsEquivalence :=
    (pbcScalarAdjunction c).isEquivalence_left_of_isEquivalence_right
  exact ⟨inferInstance, inferInstance⟩

private theorem rationalPullComposeDerived
    {C D D' T : Type*} [Category C] [Category D] [Category D'] [Category T]
    [Abelian C] [Abelian D] [Abelian D'] [Abelian T]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory D']
    [HasDerivedCategory T]
    (F : C ⥤ D) (G : D ⥤ T) (H : C ⥤ D') (I : D' ⥤ T)
    [F.Additive] [G.Additive] [H.Additive] [I.Additive]
    (LF : DerivedCategory C ⥤ DerivedCategory D)
    (LG : DerivedCategory D ⥤ DerivedCategory T)
    (LH : DerivedCategory C ⥤ DerivedCategory D')
    (LI : DerivedCategory D' ⥤ DerivedCategory T)
    (a : DerivedCategory.Q ⋙ LF ≅ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (b : DerivedCategory.Q ⋙ LG ≅ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (c : DerivedCategory.Q ⋙ LH ≅ H.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (d : DerivedCategory.Q ⋙ LI ≅ I.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (e : F ⋙ G ≅ H ⋙ I) :
    ∃ δ : LF ⋙ LG ≅ LH ⋙ LI, ∀ P : CochainComplex C ℤ,
      δ.hom.app (DerivedCategory.Q.obj P) ≫ LI.map (c.hom.app P) ≫
        d.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj P) =
      LG.map (a.hom.app P) ≫ b.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P) := by
  let a' : DerivedCategory.Q ⋙ (LF ⋙ LG) ≅
      (F ⋙ G).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    isoWhiskerRight a LG ≪≫ isoWhiskerLeft (F.mapHomologicalComplex (.up ℤ)) b
  let b' : DerivedCategory.Q ⋙ (LH ⋙ LI) ≅
      (H ⋙ I).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    isoWhiskerRight c LI ≪≫ isoWhiskerLeft (H.mapHomologicalComplex (.up ℤ)) d
  obtain ⟨δ, hδ⟩ := rationalPullDescendIso (LF ⋙ LG) (LH ⋙ LI) _ _ a' b'
    (isoWhiskerRight (NatIso.mapHomologicalComplex e (.up ℤ)) DerivedCategory.Q)
  exact ⟨δ, fun P ↦ by simpa only [a', b', Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, whiskerRight_app,
    whiskerLeft_app, Category.assoc] using hδ P⟩

omit [IsNoetherian X] [IsNoetherian Y]
  [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))] in
private theorem rationalPullCompletedLinear (g : X ⟶ Y) (a : RationalPullIntegral l E g) :
    (a.completedFunctor l E).Additive ∧
      (a.completedFunctor l E).Linear (PbcIntegralRing l E) := by
  let d := pbcIntegralDatum l E
  have : (pbcActualDerivedPull g d).Additive :=
    (pbcActualDerivedAdjunction g d).left_adjoint_additive
  have : (pbcActualDerivedPull g d).Linear (PbcIntegralRing l E) :=
    (pbcActualDerivedAdjunction g d).left_adjoint_linear
  let F := pbcConditionalIntegral d (pbcActualDerivedPull g d) a.ordinary_mem
  let e : F ≅ a.completedFunctor l E := NatIso.ofComponents
    (fun K ↦ ObjectProperty.isoMk _
      (@asIso _ _ _ _ ((pbcActualStrictCompletedPullUnit d g).app K.obj) (a.unit_isIso K)))
    (by
      intro K L f
      apply ObjectProperty.hom_ext
      exact (pbcActualStrictCompletedPullUnit d g).naturality f.hom)
  exact ⟨Functor.additive_of_iso e, Functor.linear_of_iso (PbcIntegralRing l E) e⟩

private def rationalPullRaw (g : X ⟶ Y) (a : RationalPullIntegral l E g) :
    PbcRationalCategory Y (pbcIntegralDatum l E) (pbcUniformizer l E) ⥤
      PbcRationalCategory X (pbcIntegralDatum l E) (pbcUniformizer l E) := by
  have := (rationalPullCompletedLinear l E g a).1
  have := (rationalPullCompletedLinear l E g a).2
  exact ScalarLocalization.transport (PbcIntegralRing l E) (pbcUniformizer l E)
    (a.completedFunctor l E)

omit [IsNoetherian X] [IsNoetherian Y]
  [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))] in
private theorem rationalPullRawFraction (g : X ⟶ Y) (a : RationalPullIntegral l E g)
    (K L : PbcBoundedConstructibleComplete Y (pbcIntegralDatum l E)) (f : K ⟶ L) (n : ℕ) :
    (rationalPullRaw l E g a).map (rationalPullFraction l E Y f n) =
      rationalPullFraction l E X ((a.completedFunctor l E).map f) n := by
  have := (rationalPullCompletedLinear l E g a).1
  have := (rationalPullCompletedLinear l E g a).2
  change (ScalarLocalization.transportHom (PbcIntegralRing l E) (pbcUniformizer l E)
    (a.completedFunctor l E) _ _) (_ • _) = _
  erw [_root_.map_smul]
  simp only [ScalarLocalization.transportHom]
  rfl

private def rationalPullRealizationIntegral {T : Scheme.{u}} [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (s : RationalModuleRealization l E T) :
    pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E) ⋙ s.J ≅
      ObjectProperty.ι (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)) ⋙
        pbcDerivedExtend (rationalPullScalar l E s) := by
  refine NatIso.ofComponents (fun K ↦ eqToIso (s.objects K)) ?_
  intro K L f
  have h := s.fractions K L f 0
  simp only [pow_zero, inv_one, map_one, one_smul] at h
  change s.J.map ((pbcRationalization T (pbcIntegralDatum l E)
    (pbcUniformizer l E)).map f) ≫ eqToHom (s.objects L) =
      eqToHom (s.objects K) ≫ (pbcDerivedExtend (rationalPullScalar l E s)).map f.hom
  rw [h]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

private def rationalPullTransportIntegral
    (R : Type*) [CommRing R] (p : R)
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [Linear R C] [Linear R D] (F : C ⥤ D) [F.Additive] [F.Linear R] :
    ScalarLocalization.localization R C p ⋙ ScalarLocalization.transport R p F ≅
      F ⋙ ScalarLocalization.localization R D p :=
  NatIso.ofComponents (fun _ ↦ { hom := 𝟙 _, inv := 𝟙 _ }) (by
    intro K L f
    dsimp only [Functor.comp_map, ScalarLocalization.localization,
      ScalarLocalization.transport, Iso.refl_hom]
    simp only [Category.comp_id, Category.id_comp,
      ScalarLocalization.transportHom, LinearMap.baseChange_tmul]
    rfl)

private def rationalPullUnitIso (g : X ⟶ Y) (a : RationalPullIntegral l E g) :
    ObjectProperty.ι (PbcIsBoundedConstructibleComplete Y (pbcIntegralDatum l E)) ⋙
        pbcActualDerivedPull g (pbcIntegralDatum l E) ≅
      a.completedFunctor l E ⋙
        ObjectProperty.ι (PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)) :=
  NatIso.ofComponents
    (fun K ↦ @asIso _ _ _ _
      ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) g).app K.obj) (a.unit_isIso K))
    (fun f ↦ (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) g).naturality f.hom)

private theorem rationalPullTransportIntegral_hom_app
    (R : Type*) [CommRing R] (p : R)
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [Linear R C] [Linear R D] (F : C ⥤ D) [F.Additive] [F.Linear R] (K : C) :
    (rationalPullTransportIntegral R p F).hom.app K = 𝟙 _ := by
  rfl

private theorem rationalPullRealizationIntegral_hom_app {T : Scheme.{u}} [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (s : RationalModuleRealization l E T)
    (K : PbcBoundedConstructibleComplete T (pbcIntegralDatum l E)) :
    (rationalPullRealizationIntegral l E s).hom.app K = eqToHom (s.objects K) := by
  rfl

private theorem rationalPullRealizationIntegral_inv_app {T : Scheme.{u}} [IsNoetherian T]
    [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
    [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
    (s : RationalModuleRealization l E T)
    (K : PbcBoundedConstructibleComplete T (pbcIntegralDatum l E)) :
    (rationalPullRealizationIntegral l E s).inv.app K = eqToHom (s.objects K).symm := by
  rfl

omit [IsNoetherian X] [IsNoetherian Y]
  [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))] in
private theorem rationalPullUnitIso_inv_app (g : X ⟶ Y) (a : RationalPullIntegral l E g)
    (K : PbcBoundedConstructibleComplete Y (pbcIntegralDatum l E)) :
    (rationalPullUnitIso l E g a).inv.app K =
      @CategoryTheory.inv _ _ _ _
        ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) g).app K.obj)
        (a.unit_isIso K) := by
  rfl

/-- Assemble the comparison before specializing to concrete sheaf functors. -/
private theorem rationalPullAssembleIntegral
    {IY IX RY RX DY DX EY EX : Type*}
    [Category IY] [Category IX] [Category RY] [Category RX]
    [Category DY] [Category DX] [Category EY] [Category EX]
    (QY : IY ⥤ RY) (QX : IX ⥤ RX) (raw : RY ⥤ RX) (T : IY ⥤ IX)
    (ιY : IY ⥤ DY) (ιX : IX ⥤ DX) (A : DY ⥤ DX)
    (FX : DX ⥤ EX) (FY : DY ⥤ EY) (G : EY ⥤ EX)
    (JX : RX ⥤ EX) (JY : RY ⥤ EY)
    (t : QY ⋙ raw ≅ T ⋙ QX) (x : QX ⋙ JX ≅ ιX ⋙ FX)
    (u : ιY ⋙ A ≅ T ⋙ ιX) (d : A ⋙ FX ≅ FY ⋙ G)
    (y : QY ⋙ JY ≅ ιY ⋙ FY) :
    ∃ e : QY ⋙ (raw ⋙ JX) ≅ QY ⋙ (JY ⋙ G), ∀ K : IY,
      e.hom.app K = JX.map (t.hom.app K) ≫ x.hom.app (T.obj K) ≫
        FX.map (u.inv.app K) ≫ d.hom.app (ιY.obj K) ≫ G.map (y.inv.app K) := by
  refine ⟨isoWhiskerRight t JX ≪≫ isoWhiskerLeft T x ≪≫
    isoWhiskerRight u.symm FX ≪≫ isoWhiskerLeft ιY d ≪≫
    isoWhiskerRight y.symm G, ?_⟩
  intro K
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    whiskerRight_app, whiskerLeft_app]

private theorem rationalPullNormalize
    {C D V W : Type*} [Category C] [Category D] [Category V] [Category W]
    (F : C ⥤ D) (G : V ⥤ D) (J : W ⥤ D) {A B : C} (u : A ⟶ B) [IsIso u]
    {v : W} (hx : J.obj v = F.obj B) {w w' : V} (hy : w = w')
    (a : F.obj A ⟶ G.obj w') :
    F.map u ≫ eqToHom hx.symm ≫ J.map (𝟙 v) ≫ J.map (𝟙 v) ≫ eqToHom hx ≫
      F.map (asIso u).inv ≫ a ≫ G.map (eqToHom hy.symm) ≫ G.map (eqToHom hy) = a := by
  rw [J.map_id]
  simp only [Category.id_comp, eqToHom_trans_assoc, eqToHom_refl]
  rw [← G.map_comp, eqToHom_trans, eqToHom_refl, G.map_id, Category.comp_id]
  rw [← F.map_comp_assoc]
  change F.map (u ≫ CategoryTheory.inv u) ≫ a = a
  rw [IsIso.hom_inv_id, F.map_id, Category.id_comp]

/-- Keep functor associativity out of the kernel check of the concrete comparison. -/
private theorem rationalPullCompositeFactors
    {C D T : Type*} [Category C] [Category D] [Category T]
    [Abelian C] [Abelian D] [Abelian T]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory T]
    (F : C ⥤ D) (G : D ⥤ T) [F.Additive] [G.Additive]
    (LF : DerivedCategory C ⥤ DerivedCategory D)
    (LG : DerivedCategory D ⥤ DerivedCategory T)
    (a : DerivedCategory.Q ⋙ LF ≅ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (b : DerivedCategory.Q ⋙ LG ≅ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) :
    ∃ e : DerivedCategory.Q ⋙ (LF ⋙ LG) ≅
      (F ⋙ G).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q,
      ∀ P : CochainComplex C ℤ,
        e.hom.app P = LG.map (a.hom.app P) ≫
          b.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) := by
  refine ⟨isoWhiskerRight a LG ≪≫
    isoWhiskerLeft (F.mapHomologicalComplex (.up ℤ)) b, ?_⟩
  intro P
  rfl

private theorem rationalPullDerivedComparison (g : X ⟶ Y)
    (sX : RationalModuleRealization l E X) (sY : RationalModuleRealization l E Y)
    (eM : pbcActualModulePull g (pbcIntegralDatum l E) ⋙
      pbcExtend (rationalPullScalar l E sX) ≅
    pbcExtend (rationalPullScalar l E sY) ⋙
      rationalPullModule l E g (rationalContinuousPullback l E g)) :
    ∃ eD : pbcActualDerivedPull g (pbcIntegralDatum l E) ⋙
      pbcDerivedExtend (rationalPullScalar l E sX) ≅
    pbcDerivedExtend (rationalPullScalar l E sY) ⋙
      rationalPullDerived l E g (rationalContinuousPullback l E g),
      ∀ P : CochainComplex
      (pbcModules Y (pbcAdicCompletion Y (pbcIntegralDatum l E))) ℤ,
    eD.hom.app (DerivedCategory.Q.obj P) ≫
        (rationalPullDerived l E g (rationalContinuousPullback l E g)).map
            (pbcComplexCounit (rationalPullScalar l E sY) P) ≫
        rationalPullComplexCounit l E g (rationalContinuousPullback l E g)
            (((pbcExtend (rationalPullScalar l E sY)).mapHomologicalComplex (.up ℤ)).obj P) =
      (pbcDerivedExtend (rationalPullScalar l E sX)).map
          (pbcActualPullComplexCounit g (pbcIntegralDatum l E) P) ≫
        pbcComplexCounit (rationalPullScalar l E sX)
          (((pbcActualModulePull g (pbcIntegralDatum l E)).mapHomologicalComplex
            (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex eM (.up ℤ)).hom.app P) := by
  let d := pbcIntegralDatum l E
  let c := rationalContinuousPullback l E g
  have := sX.ordinary_exact.1
  have := sX.ordinary_exact.2
  have := sY.ordinary_exact.1
  have := sY.ordinary_exact.2
  have := (rationalPullExtendExact c).1
  have := (rationalPullExtendExact c).2
  let q := proEtaleRingModulePullback g (rationalCoefficientSheaf l Y E)
    ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
      (rationalCoefficientSheaf l Y E)) (Iso.refl _)
  obtain ⟨eq, heq⟩ := rationalPullCompositeFactors q (pbcExtend c)
    (adicTowerPullback g (rationalCoefficientSheaf l Y E)) (pbcDerivedExtend c)
    (proEtaleRingDerivedPullbackFactors g (rationalCoefficientSheaf l Y E)
      ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
        (rationalCoefficientSheaf l Y E)) (Iso.refl _)) (rationalPullScalarFactors c)
  obtain ⟨eD, heD⟩ := rationalPullComposeDerived
    (pbcActualModulePull g d) (pbcExtend (rationalPullScalar l E sX))
    (pbcExtend (rationalPullScalar l E sY)) (rationalPullModule l E g c)
    (pbcActualDerivedPull g d) (pbcDerivedExtend (rationalPullScalar l E sX))
    (pbcDerivedExtend (rationalPullScalar l E sY)) (rationalPullDerived l E g c)
    (rationalPullOrdinaryFactors l E g) (rationalPullScalarFactors _)
    (rationalPullScalarFactors _) eq eM
  refine ⟨eD, ?_⟩
  intro P
  simpa only [heq, rationalPullScalarFactors_app, rationalPullOrdinaryFactors_app,
    rationalPullComplexCounit] using heD P

/-- Rational realization commutes with the specified completed pullback for any morphism.
Source: Bhatt--Scholze, Proposition 6.6.11, Lemma 6.5.9 and Remark 6.8.15,
pp. 50, 54, 62 (blueprint: lem-per-rational-realization-pullback-comparison).

Proof (the seven steps of the node):
1. Apply lem-weil-pbc-integral-stratified-perfect-characterization and
lem-tw-ordinary-pullback-stratified-models. Pull back strata and covers, discarding
empty strata. The same perfect A-complex gives each new local model. Reverse the
characterization to retain completeness, uniform bounds and compatible etale witnesses.
2. Finite coefficient quotients and lem-weil-pbc-profinite-coefficient-inverse-image
identify the projection-defined coefficient map. Apply
lem-weil-pbc-reduction-pullback-derived-tower: its augmentation equation identifies
Rlim(tau) composed with the specified unit with the ordinary object's quotient unit.
This is an equality of induced maps, not an inference from their projections.
lem-weil-pbc-intrinsic-to-tower-complete makes that unit invertible by step 1.
3. Choose a flat-term K-flat resolution by lem-pc-kflat-resolution. The inverse-image,
coefficient-extension and localization operations preserve its resolving class by
lem-weil-pbc-ringed-topos-kflat-pullback. Use
lem-weil-pbc-ringed-topoi-derived-pullback to compute the derived operations.
4. Flatten u tensor (s tensor n) to us tensor n; the inverse inserts one.
5. Use lem-weil-pbc-localization-inverse-image-coherence to identify the pulled
localization with localization of the pulled ring, preserving the unit. Flatten
u tensor (r/varpi^m tensor n) to u c(r) varpi^(-m) tensor n. Both ordinary sides
thus identify with E_X tensor over g inverse B_Y of g inverse K. Sheafify these
balanced maps; their natural chain isomorphism has the stated derived normalization.
6. Compose this comparison with realization of the inverse strict completion unit.
The displayed alpha_normalization is this formula precomposed with realization
of that invertible unit, with the recorded object formulas inserted.
7. The coefficient maps preserve constant A-scalars. Apply
lem-pur-ringed-derived-pullback-linear, then conjugate by the invertible natural
units to obtain A-linearity of completed pullback. Extend f/varpi^n by the same
denominator; the annihilating-power criterion proves independence of representative.
Multiply integral naturality by varpi^(-n), using the realization fraction formula.
This yields the raw natural isomorphism. No coefficient isomorphism is assumed. -/
theorem rationalRealizationPullbackComparison (g : X ⟶ Y)
    (sX : RationalModuleRealization l E X) (sY : RationalModuleRealization l E Y) :
    Nonempty (RationalRealizationPullbackComparison l E g sX sY) := by
  let d := pbcIntegralDatum l E
  let c := rationalContinuousPullback l E g
  let integral := rationalPullIntegralData l E g
  obtain ⟨eM, heM⟩ := rationalPullModuleComparison l E g sX sY
  obtain ⟨eD, heD⟩ := rationalPullDerivedComparison l E g sX sY eM
  have := (rationalPullCompletedLinear l E g integral).1
  have := (rationalPullCompletedLinear l E g integral).2
  let raw := rationalPullRaw l E g integral
  let QY := pbcRationalization Y d (pbcUniformizer l E)
  let ιY := ObjectProperty.ι (PbcIsBoundedConstructibleComplete Y d)
  obtain ⟨eInt, heInt⟩ := rationalPullAssembleIntegral
    QY (pbcRationalization X d (pbcUniformizer l E)) raw
    (integral.completedFunctor l E) ιY
    (ObjectProperty.ι (PbcIsBoundedConstructibleComplete X d))
    (pbcActualDerivedPull g d) (pbcDerivedExtend (rationalPullScalar l E sX))
    (pbcDerivedExtend (rationalPullScalar l E sY)) (rationalPullDerived l E g c) sX.J sY.J
    (rationalPullTransportIntegral (PbcIntegralRing l E) (pbcUniformizer l E)
      (integral.completedFunctor l E)) (rationalPullRealizationIntegral l E sX)
    (rationalPullUnitIso l E g integral) eD (rationalPullRealizationIntegral l E sY)
  have := (pbcIntegralUniformComplete_isTriangulated l E Y Fact.out Fact.out).2
  obtain ⟨α, hα, _⟩ := ScalarLocalization.naturalIso_of_integral
    (PbcIntegralRing l E) (PbcBoundedConstructibleComplete Y d) (pbcUniformizer l E)
    (raw ⋙ sX.J) (sY.J ⋙ rationalPullDerived l E g c) eInt
  refine ⟨{
    integral := integral
    rationalCoefficient := c
    rational_normalization := rationalContinuousPullback_normalized l E g
    coefficient_square := rationalPullCoefficientSquare l E g sX sY
    moduleComparison := eM
    module_unit := heM
    ordinaryComparison := eD
    derived_normalization := ?_
    rawPull := raw
    raw_objects := fun _ ↦ rfl
    raw_fractions := ?_
    alpha := α
    alpha_normalization := ?_
  }⟩
  · intro P
    exact heD P
  · intro K L f n
    simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using
      rationalPullRawFraction l E g integral K L f n
  · intro K
    rw [hα]
    have := integral.unit_isIso K
    rw [heInt]
    simp only [rationalPullTransportIntegral_hom_app,
      rationalPullRealizationIntegral_hom_app, rationalPullRealizationIntegral_inv_app,
      rationalPullUnitIso_inv_app, eqToHom_refl, Category.assoc]
    exact rationalPullNormalize (pbcDerivedExtend (rationalPullScalar l E sX))
      (rationalPullDerived l E g c) sX.J
      ((pbcActualStrictCompletedPullUnit d g).app K.obj)
      (sX.objects ((integral.completedFunctor l E).obj K)) (sY.objects K)
      (eD.hom.app K.obj)

end AlgebraicGeometry.Scheme
