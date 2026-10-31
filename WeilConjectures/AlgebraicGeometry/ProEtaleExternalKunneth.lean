/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.EtaleProEtaleExceptionalTransport
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExternalProduct
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat

public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import WeilConjectures.AlgebraicGeometry.OrdinaryEtaleKunneth
public import WeilConjectures.AlgebraicGeometry.FiniteProductProjectionBaseChange
import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparison
import WeilConjectures.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules
import WeilConjectures.AlgebraicGeometry.AffineLocallyConstructibleProEtaleModules
import WeilConjectures.AlgebraicGeometry.CoefficientConstructibleEtaleModules
import WeilConjectures.AlgebraicGeometry.ConstructibleNoetherianEtaleModules
import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
import WeilConjectures.AlgebraicGeometry.ProEtaleTorAmplitude
import WeilConjectures.AlgebraicGeometry.ProEtaleSmallModelComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleRingedComparisonInjectiveAcyclicity
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
import WeilConjectures.AlgebraicGeometry.ProEtaleRingInverseImage
import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientsSupplement
import WeilConjectures.AlgebraicGeometry.ConstantCompletionEquivalence
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
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
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.ConstantCoefficientScalarExtension
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsSupplement
import WeilConjectures.AlgebraicGeometry.StrictPerfectCoefficientPackageSupplement
import WeilConjectures.AlgebraicGeometry.SfIntrinsicRealizationTransport
import WeilConjectures.AlgebraicGeometry.ClassicalContinuityMapSupplement
import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
import WeilConjectures.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
import WeilConjectures.AlgebraicGeometry.ProEtaleBoundedConstructible
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonData
import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonLocal
import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleFiniteLocalModelsPullback
import WeilConjectures.CategoryTheory.CoefficientFiniteLocalSystemsPullback
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.AlgebraicGeometry.EtaleStratificationLocalGluingCore
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Algebra.Module.FinitePresentation
import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonClassical
import WeilConjectures.AlgebraicGeometry.CoefficientStratifiedContinuity
import WeilConjectures.AlgebraicGeometry.CoefficientFpLocalSystemOrigin
import WeilConjectures.AlgebraicGeometry.CoefficientFpLocalSystemEtaleCover
import Mathlib.CategoryTheory.Sites.CoversTop.Basic
import WeilConjectures.AlgebraicGeometry.CoefficientLocallyConstantEtaleSections
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.AlgebraicGeometry.CoefficientLocallyConstantCounit
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Limits.Presheaf
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import Mathlib.CategoryTheory.Sites.Precoverage.Generates
import Mathlib.CategoryTheory.Sites.Finite
import Mathlib.CategoryTheory.Sites.LocalProperties
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.Data.Finite.Prod
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Sites.SheafHom
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonConstantChartCounit
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.AlgebraicGeometry.CoefficientStratifiedEssentialImage
import WeilConjectures.AlgebraicGeometry.CoefficientOriginOpenCover
import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful
import Mathlib.CategoryTheory.Category.ULift
import WeilConjectures.AlgebraicGeometry.CoefficientOriginAffineOpenClosed
import WeilConjectures.AlgebraicGeometry.CoefficientOriginClosedDirectImage
import WeilConjectures.AlgebraicGeometry.FiniteComparisonModelRealizationSupplement
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonContinuity
import WeilConjectures.SixFunctors.ProEtale.Comparison.Continuity
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonRepresentableContinuity
import WeilConjectures.AlgebraicGeometry.ProEtaleClassicalSheavesImage
import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleComparisonSections
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.CategoryTheory.LanContinuityFromRepresentables
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.AlgebraicGeometry.AffinePresentationSectionColimit
import WeilConjectures.AlgebraicGeometry.AffineEtaleLargeLimitMaps
import WeilConjectures.AlgebraicGeometry.AffineEtaleLargeLimitFactorization
import WeilConjectures.AlgebraicGeometry.AffineEtaleLargeLimitEquality
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.Topology.Spectral.ConstructibleTopology
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.RingTheory.IndEtaleSmallIndex
import WeilConjectures.RingTheory.ProEtale.Etale
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.CategoryTheory.Limits.FinallySmall
import Mathlib.CategoryTheory.Functor.OfSequence
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonPresentationSheafification
import WeilConjectures.AlgebraicGeometry.CoefficientClassicalModuleOrigin
import WeilConjectures.AlgebraicGeometry.CoefficientOriginLocalizationKernel
import WeilConjectures.AlgebraicGeometry.CoefficientFixedLocalizationKernelComparison
import WeilConjectures.AlgebraicGeometry.CoefficientFixedClosedUnitEpi
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Detection
import WeilConjectures.AlgebraicGeometry.ProEtale.ClosedSiteAdjunction
import WeilConjectures.AlgebraicGeometry.CoefficientOpenClosedKernel
import WeilConjectures.AlgebraicGeometry.CoefficientOpenExtension
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Small
import Mathlib.CategoryTheory.Adjunction.Triple
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonInjectiveAcyclic
import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
import WeilConjectures.AlgebraicGeometry.ConstructibleComparisonModuleExact
import WeilConjectures.CategoryTheory.ModuleInverseImageUnitComparison
import Mathlib.Algebra.Category.Ring.Limits
import WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import WeilConjectures.CategoryTheory.ModuleInverseImageAction
import WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonAffineSections
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonAffineCech
import WeilConjectures.CategoryTheory.SiteCechComplex
import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
import WeilConjectures.AlgebraicGeometry.CoefficientAffineCechPresentation
import WeilConjectures.AlgebraicGeometry.CoefficientAffineCechSystem
import WeilConjectures.AlgebraicGeometry.CechNervePresentationConstruction
import WeilConjectures.AlgebraicGeometry.AffineComparisonEtaleCechSystem
import WeilConjectures.CategoryTheory.Sites.CechComplex
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import WeilConjectures.CategoryTheory.Pro.Generating
import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.CategoryTheory.Sites.CechComplexRelativeLimit
import WeilConjectures.CategoryTheory.InjectiveModulePresheaf
import WeilConjectures.CategoryTheory.Sites.InjectivePresheafModuleCechExact
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.Algebra.Homology.ShortComplex.Ab
import WeilConjectures.CategoryTheory.ModuleCechCriterion
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Abelian.RightDerived
import WeilConjectures.CategoryTheory.SiteSesCechH1Surjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunctionAcyclic
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ConstructiblePartitionLocalClosedStratum
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Topology.Constructible
import WeilConjectures.Topology.ConstructibleIsRetrocompact
import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonModuleEquivalence
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonModuleCriteria
import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonDerivedFunctor
import WeilConjectures.AlgebraicGeometry.CoefficientClassicalSingle
import WeilConjectures.AlgebraicGeometry.CoefficientBoundedClassicalDescent
import WeilConjectures.CategoryTheory.DerivedCategory.PlusDevissage
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonConstructibilityTest
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonFixedPullback
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonFiniteReflection
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonConstantChartReflection
import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleConstructibleIso
import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonDerivedEquivalence
import WeilConjectures.AlgebraicGeometry.ProEtaleDirectImageComparison
import WeilConjectures.AlgebraicGeometry.BoundedBelowProEtaleComparison
import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinaryEquivalence
import WeilConjectures.AlgebraicGeometry.InternalModuleOperationsTransportSupplement
import WeilConjectures.AlgebraicGeometry.FiniteCoverTensorCounitComparison
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleFinitePushforwardEmbedding
import WeilConjectures.AlgebraicGeometry.FiniteConstructiblePushforwardKunneth
import WeilConjectures.CategoryTheory.ExactDeltaEmbeddingDetection
import WeilConjectures.AlgebraicGeometry.ConstructibleCoefficientSerre
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.SixFunctors.FlatModel
import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsSupplement
import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.CategoryTheory.GeometricRingTransport
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIsoSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed

/-!
# Ordinary external Künneth on the small pro-étale site

Source: literature/blueprint/latest/blueprint/sec-six-functors/
sk-lem-sf-kunneth-star/_section.md and sk-lem-sf-kunneth-star.proof.md
(blueprint: sk-lem-sf-kunneth-star).

The maps are the adjuncts of the specified tensor products of counits. The coefficients
are ordinary finite-ring module sheaves, and the domain predicate is the recorded intrinsic
bounded constructible finite-Tor predicate. No coefficient system is introduced.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.ProEtale

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- Pull back the ordinary derived counit across a commutative square.
Source: current blueprint, displayed adjunct of (1)
(blueprint: sk-lem-sf-kunneth-star). -/
def externalKunnethPulledCounit
    {X Y W Z : Scheme.{u}} {f : X ⟶ Y} {p : W ⟶ X} {h : W ⟶ Z} {q : Z ⟶ Y}
    (sq : CommSq p h f q)
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) :
    (upperStar (ModuleCat.{u + 1} A) h).leftDerivedFunctor.obj
        ((upperStar (ModuleCat.{u + 1} A) q).leftDerivedFunctor.obj
          ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj M)) ⟶
      (upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj M :=
  (leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} A) sq).hom.app _ ≫
    (upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).counit.app M)

/-- The two-morphism external Künneth arrow on a pair of commuting projection squares.
It is the derived adjunction mate of the tensor product of the two pulled-back counits.
Source: current blueprint, statement and final paragraph of the proof
(blueprint: sk-lem-sf-kunneth-star). -/
def externalKunnethMap
    {X₁ X₂ Y₁ Y₂ W Z : Scheme.{u}}
    {f₁ : X₁ ⟶ Y₁} {f₂ : X₂ ⟶ Y₂} {h : W ⟶ Z}
    {p₁ : W ⟶ X₁} {p₂ : W ⟶ X₂} {q₁ : Z ⟶ Y₁} {q₂ : Z ⟶ Y₂}
    (sq₁ : CommSq p₁ h f₁ q₁) (sq₂ : CommSq p₂ h f₂ q₂)
    (M₁ : DerivedCategory (Sheaf (Scheme.ProEt.topology X₁) (ModuleCat.{u + 1} A)))
    (M₂ : DerivedCategory (Sheaf (Scheme.ProEt.topology X₂) (ModuleCat.{u + 1} A))) :
    (upperStar (ModuleCat.{u + 1} A) q₁).leftDerivedFunctor.obj
        ((lowerStar (ModuleCat.{u + 1} A) f₁).rightDerivedFunctor.obj M₁) ⊗
      (upperStar (ModuleCat.{u + 1} A) q₂).leftDerivedFunctor.obj
        ((lowerStar (ModuleCat.{u + 1} A) f₂).rightDerivedFunctor.obj M₂) ⟶
    (lowerStar (ModuleCat.{u + 1} A) h).rightDerivedFunctor.obj
      ((upperStar (ModuleCat.{u + 1} A) p₁).leftDerivedFunctor.obj M₁ ⊗
        (upperStar (ModuleCat.{u + 1} A) p₂).leftDerivedFunctor.obj M₂) :=
  (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h).homEquiv _ _
    ((leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) h _ _).hom ≫
      tensorHom (externalKunnethPulledCounit A sq₁ M₁)
        (externalKunnethPulledCounit A sq₂ M₂))

/-- The identity-factor arrow, with the identity on the second tensor factor.
Source: current blueprint, formula (1) and its displayed adjunct
(blueprint: sk-lem-sf-kunneth-star). -/
def externalKunnethIdentityMap
    {X Y T W Z : Scheme.{u}} {f : X ⟶ Y} {p : W ⟶ X} {h : W ⟶ Z}
    {q : Z ⟶ Y} {t : W ⟶ T} {s : Z ⟶ T}
    (sq : CommSq p h f q) (w : h ≫ s = t)
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (Q : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))) :
    (upperStar (ModuleCat.{u + 1} A) q).leftDerivedFunctor.obj
        ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj M) ⊗
      (upperStar (ModuleCat.{u + 1} A) s).leftDerivedFunctor.obj Q ⟶
    (lowerStar (ModuleCat.{u + 1} A) h).rightDerivedFunctor.obj
      ((upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj M ⊗
        (upperStar (ModuleCat.{u + 1} A) t).leftDerivedFunctor.obj Q) :=
  (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h).homEquiv _ _
    ((leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) h _ _).hom ≫
      tensorHom (externalKunnethPulledCounit A sq M)
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) h s).inv.app Q ≫
          (leftDerivedUpperStarCongr (ModuleCat.{u + 1} A) w).hom.app Q))

/-- Ordinary external Künneth for two morphisms over the geometric finite field.
Source: current blueprint, sk-lem-sf-kunneth-star, first displayed map
(blueprint: sk-lem-sf-kunneth-star).

Proof:
1. Define the identity-factor map by its counit adjunct. For constant second factor,
   independent base change makes it invertible. The constructible and direct-image
   comparison theorems identify the étale and pro-étale maps and their counits; the
   finite-ring module-object equivalence identifies the ordinary coefficient operations.
2. Over a finite field of coefficients, finite direct images and finite sums reduce to
   constants. Embed each constructible sheaf into such a sum. The exact/delta embedding
   criterion proves injectivity in every degree and surjectivity by degree induction.
3. Exactness in each variable and bounded truncation triangles extend this to bounded
   constructible complexes. Over a field the truncations have finite Tor amplitude;
   bounded flat models give the same extension.
4. Over a finite ring, stability makes both endpoints bounded constructible of finite
   Tor amplitude. Scalar comparison respects the defining counits. Every residue-field
   reduction is the field-coefficient map, so residue conservativity kills its cone.
5. Factor the product morphism into its two identity-factor morphisms. Stability puts
   the intermediate direct image in the required domain. Under composition the adjunct
   is the tensor of the two counits, so the composite is exactly the specified map.
-/
theorem isIso_externalKunnethMap
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) (_hl : l.Prime)
    (_hne : l ≠ ringChar D.k)
    (_hA : ∃ n : ℕ, 0 < n ∧ ((l ^ n : ℕ) : A) = 0)
    {X₁ X₂ Y₁ Y₂ : Scheme.{u}}
    (b₁ : Y₁ ⟶ Spec (.of D.k)) (b₂ : Y₂ ⟶ Spec (.of D.k))
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    [LocallyOfFiniteType b₁] [QuasiCompact b₁] [IsSeparated b₁]
    [LocallyOfFiniteType b₂] [QuasiCompact b₂] [IsSeparated b₂]
    [LocallyOfFiniteType (f₁ ≫ b₁)] [QuasiCompact (f₁ ≫ b₁)] [IsSeparated (f₁ ≫ b₁)]
    [LocallyOfFiniteType (f₂ ≫ b₂)] [QuasiCompact (f₂ ≫ b₂)] [IsSeparated (f₂ ≫ b₂)]
    (M₁ : DerivedCategory (Sheaf (Scheme.ProEt.topology X₁) (ModuleCat.{u + 1} A)))
    (M₂ : DerivedCategory (Sheaf (Scheme.ProEt.topology X₂) (ModuleCat.{u + 1} A)))
    (_hM₁ : exceptionalTransportProEtaleObjects A X₁ M₁)
    (_hM₂ : exceptionalTransportProEtaleObjects A X₂ M₂) :
    IsIso (externalKunnethMap A
      ⟨(pullback.mapOverBase_fst f₁ f₂ b₁ b₂).symm⟩
      ⟨(pullback.mapOverBase_snd f₁ f₂ b₁ b₂).symm⟩ M₁ M₂) := by
  sorry

/-- The identity-factor ordinary external Künneth map is invertible.
Source: current blueprint, sk-lem-sf-kunneth-star, formula (1)
(blueprint: sk-lem-sf-kunneth-star).

Proof: Use steps 1--4 of the preceding theorem's proof: independent base change for
constants, finite-cover embedding and induction for sheaves over a finite field,
bounded truncation for complexes, then scalar comparison and residue conservativity
for finite rings. The adjunct is the pulled-back first counit tensored with identity,
so this is the prescribed identity-factor map, with no choice of an isomorphism.
-/
theorem isIso_externalKunnethIdentityMap
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) (_hl : l.Prime)
    (_hne : l ≠ ringChar D.k)
    (_hA : ∃ n : ℕ, 0 < n ∧ ((l ^ n : ℕ) : A) = 0)
    {X Y T : Scheme.{u}} (b : Y ⟶ Spec (.of D.k)) (c : T ⟶ Spec (.of D.k))
    (f : X ⟶ Y)
    [LocallyOfFiniteType b] [QuasiCompact b] [IsSeparated b]
    [LocallyOfFiniteType c] [QuasiCompact c] [IsSeparated c]
    [LocallyOfFiniteType (f ≫ b)] [QuasiCompact (f ≫ b)] [IsSeparated (f ≫ b)]
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (Q : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)))
    (_hM : exceptionalTransportProEtaleObjects A X M)
    (_hQ : exceptionalTransportProEtaleObjects A T Q) :
    IsIso (externalKunnethIdentityMap A
      ⟨(pullback.mapOverBaseRight_fst f b c).symm⟩
      (pullback.mapOverBaseRight_snd f b c) M Q) := by
  sorry

omit [Finite A] in
private theorem externalKunnethPulledCounit_naturality
    {X Y W Z : Scheme.{u}} {f : X ⟶ Y} {p : W ⟶ X} {h : W ⟶ Z} {q : Z ⟶ Y}
    (sq : CommSq p h f q)
    {M N : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))}
    (a : M ⟶ N) :
    (upperStar (ModuleCat.{u + 1} A) h).leftDerivedFunctor.map
        ((upperStar (ModuleCat.{u + 1} A) q).leftDerivedFunctor.map
          ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.map a)) ≫
      externalKunnethPulledCounit A sq N =
    externalKunnethPulledCounit A sq M ≫
      (upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.map a := by
  exact (Functor.whiskerLeft
    (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor
    (leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} A) sq).hom ≫
    Functor.whiskerRight
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).counit
      (upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor).naturality a

private theorem externalKunnethTensor_naturality
    {W Z : Scheme.{u}} (h : W ⟶ Z)
    {M N Q R : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A))}
    (a : M ⟶ N) (b : Q ⟶ R) :
    (upperStar (ModuleCat.{u + 1} A) h).leftDerivedFunctor.map (tensorHom a b) ≫
        (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) h N R).hom =
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) h M Q).hom ≫
        tensorHom ((upperStar (ModuleCat.{u + 1} A) h).leftDerivedFunctor.map a)
          ((upperStar (ModuleCat.{u + 1} A) h).leftDerivedFunctor.map b) := by
  let τ := (leftDerivedUpperStarTensorNatIso (ModuleCat.{u + 1} A) h).hom
  have ha := congrArg (fun α ↦ α.app Q) (τ.naturality a)
  have hb := (τ.app N).naturality b
  change (upperStar (ModuleCat.{u + 1} A) h).leftDerivedFunctor.map (a ▷ Q) ≫
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) h N Q).hom =
    (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) h M Q).hom ≫
      ((upperStar (ModuleCat.{u + 1} A) h).leftDerivedFunctor.map a ▷
        (upperStar (ModuleCat.{u + 1} A) h).leftDerivedFunctor.obj Q) at ha
  change (upperStar (ModuleCat.{u + 1} A) h).leftDerivedFunctor.map (N ◁ b) ≫
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) h N R).hom =
    (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) h N Q).hom ≫
      ((upperStar (ModuleCat.{u + 1} A) h).leftDerivedFunctor.obj N ◁
        (upperStar (ModuleCat.{u + 1} A) h).leftDerivedFunctor.map b) at hb
  simp only [MonoidalCategory.tensorHom_def, Functor.map_comp, Category.assoc]
  rw [hb, ← Category.assoc, ha, Category.assoc]

/-- Naturality of the two-counit Künneth arrow in both coefficient complexes.
Source: current blueprint, sk-lem-sf-kunneth-star, naturality clause
(blueprint: sk-lem-sf-kunneth-star).

Proof: Naturality of each derived counit, each pullback square comparison and the tensor
comparison gives naturality of the adjunct. The adjunction Hom equivalence is natural
in its source and target, so transposing gives the displayed equality.
-/
theorem externalKunnethMap_naturality
    {X₁ X₂ Y₁ Y₂ W Z : Scheme.{u}}
    {f₁ : X₁ ⟶ Y₁} {f₂ : X₂ ⟶ Y₂} {h : W ⟶ Z}
    {p₁ : W ⟶ X₁} {p₂ : W ⟶ X₂} {q₁ : Z ⟶ Y₁} {q₂ : Z ⟶ Y₂}
    (sq₁ : CommSq p₁ h f₁ q₁) (sq₂ : CommSq p₂ h f₂ q₂)
    {M₁ N₁ : DerivedCategory (Sheaf (Scheme.ProEt.topology X₁) (ModuleCat.{u + 1} A))}
    {M₂ N₂ : DerivedCategory (Sheaf (Scheme.ProEt.topology X₂) (ModuleCat.{u + 1} A))}
    (a : M₁ ⟶ N₁) (b : M₂ ⟶ N₂) :
    tensorHom
        ((upperStar (ModuleCat.{u + 1} A) q₁).leftDerivedFunctor.map
          ((lowerStar (ModuleCat.{u + 1} A) f₁).rightDerivedFunctor.map a))
        ((upperStar (ModuleCat.{u + 1} A) q₂).leftDerivedFunctor.map
          ((lowerStar (ModuleCat.{u + 1} A) f₂).rightDerivedFunctor.map b)) ≫
      externalKunnethMap A sq₁ sq₂ N₁ N₂ =
    externalKunnethMap A sq₁ sq₂ M₁ M₂ ≫
      (lowerStar (ModuleCat.{u + 1} A) h).rightDerivedFunctor.map
        (tensorHom ((upperStar (ModuleCat.{u + 1} A) p₁).leftDerivedFunctor.map a)
          ((upperStar (ModuleCat.{u + 1} A) p₂).leftDerivedFunctor.map b)) := by
  unfold externalKunnethMap
  apply Adjunction.homEquiv_naturality_left_square
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h)
  rw [← Category.assoc, externalKunnethTensor_naturality]
  simp only [Category.assoc, tensorHom_comp_tensorHom,
    externalKunnethPulledCounit_naturality]

/-- Naturality of the identity-factor Künneth arrow in its two inputs.
Source: current blueprint, sk-lem-sf-kunneth-star, naturality clause
(blueprint: sk-lem-sf-kunneth-star).

Proof: The pulled-back counit, composition comparison and tensor comparison are natural.
Their tensor composite is therefore natural, and naturality of the adjunction Hom
bijection transports that equation to the stated equality.
-/
theorem externalKunnethIdentityMap_naturality
    {X Y T W Z : Scheme.{u}} {f : X ⟶ Y} {p : W ⟶ X} {h : W ⟶ Z}
    {q : Z ⟶ Y} {t : W ⟶ T} {s : Z ⟶ T}
    (sq : CommSq p h f q) (w : h ≫ s = t)
    {M N : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))}
    {Q R : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))}
    (a : M ⟶ N) (b : Q ⟶ R) :
    tensorHom
        ((upperStar (ModuleCat.{u + 1} A) q).leftDerivedFunctor.map
          ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.map a))
        ((upperStar (ModuleCat.{u + 1} A) s).leftDerivedFunctor.map b) ≫
      externalKunnethIdentityMap A sq w N R =
    externalKunnethIdentityMap A sq w M Q ≫
      (lowerStar (ModuleCat.{u + 1} A) h).rightDerivedFunctor.map
        (tensorHom ((upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.map a)
          ((upperStar (ModuleCat.{u + 1} A) t).leftDerivedFunctor.map b)) := by
  have hb := ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) h s).inv ≫
    (leftDerivedUpperStarCongr (ModuleCat.{u + 1} A) w).hom).naturality b
  simp only [Functor.comp_map, NatTrans.comp_app] at hb
  unfold externalKunnethIdentityMap
  apply Adjunction.homEquiv_naturality_left_square
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h)
  rw [← Category.assoc, externalKunnethTensor_naturality]
  simp only [Category.assoc, tensorHom_comp_tensorHom,
    externalKunnethPulledCounit_naturality, hb]

end AlgebraicGeometry.ProEtale
