/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralConstantCompletion
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionEquivalence
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtaleRingInverseImage
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientData
public import WeilConjectures.AlgebraicGeometry.ProEtalePointPullbackSupplement
public import WeilConjectures.Topology.ContinuousMapCondensedRingSupplement
public import WeilConjectures.NumberTheory.Padics.IntegersProfiniteTower
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Compactness.Compact
public import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
public import Mathlib.Topology.Bases
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.NumberTheory.Padics.ProperSpace
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
public import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.Topology.Category.Profinite.AsLimit
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Topology.Category.Profinite.CofilteredLimit
public import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
public import WeilConjectures.AlgebraicGeometry.ProfiniteLocallyConstantAdjunction
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteConstantRepresentable
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.FintypeCat
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import WeilConjectures.AlgebraicGeometry.CoproductCopiesMorphismsClopen
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralRingComparison
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralPointRingMap
public import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Monoidal.Mon
public import WeilConjectures.SixFunctors.ProEtale.DerivedCompletionSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
public import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
public import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Cones
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
public import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Adjunction.Unique
public import WeilConjectures.AlgebraicGeometry.ProEtaleTorAmplitudePresentations
public import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtaleSmallModelComparison
public import WeilConjectures.AlgebraicGeometry.ProEtaleRingedComparisonInjectiveAcyclicity
public import WeilConjectures.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import WeilConjectures.AlgebraicGeometry.ProEtaleBoundedConstructible
public import WeilConjectures.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules
public import WeilConjectures.AlgebraicGeometry.AffineLocallyConstructibleProEtaleModules
public import WeilConjectures.AlgebraicGeometry.CoefficientConstructibleEtaleModules
public import WeilConjectures.AlgebraicGeometry.ConstructibleNoetherianEtaleModules
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.CategoryTheory.ConstantCoefficientScalarExtension
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsSupplement
public import WeilConjectures.AlgebraicGeometry.StrictPerfectCoefficientPackageSupplement
public import WeilConjectures.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonData
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleConstructibleIso
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
import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleFiniteLocalModelsPullback
import WeilConjectures.CategoryTheory.CoefficientFiniteLocalSystemsPullback
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Algebra.Module.FinitePresentation
import WeilConjectures.AlgebraicGeometry.ConstantFieldTorBounds
import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparison
import WeilConjectures.AlgebraicGeometry.ClassicalContinuityMapSupplement
import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
import WeilConjectures.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
import WeilConjectures.AlgebraicGeometry.ProEtaleBoundedConstructible
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonData
import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonLocal
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.AlgebraicGeometry.EtaleStratificationLocalGluingCore
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
import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonDerivedEquivalence

/-! # Residue comparison for integral restriction of scalars

Source: blueprint latest, sec-six-functors-basics/sk-lem-integral-models,
`sk-lem-integral-models-stacks.proof.md`, the finite-reduction and field-Tor paragraphs
(blueprint: lem-sfb-integral-stacks-residue-comparison).

We use the published coefficient-sized small site and its standard derived localization.
The finite-level index zero denotes exponent one. The comparison is specified by the
pure-tensor formula and its computation on flat-term K-flat representatives, so the
isomorphism retains the residue coefficient action.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ConstantCompletion

namespace AlgebraicGeometry.ProEtale.IntegralStacksResidueComparison

open IntegralConstantCompletion

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The Noetherian structure inherited from the recorded DVR, transported through ULift.
This is the existing principal-ideal-ring Noetherian instance, with its DVR hypothesis
supplied by the coefficient construction; no new coefficient assumption is made.
Source: blueprint latest, integral-models Stacks proof, residue coefficient notation;
Serre, Local Fields, Chapter II, §2
(blueprint: lem-sfb-integral-stacks-residue-comparison). -/
instance integersNoetherian : IsNoetherianRing (integers l E) :=
  @isNoetherianRing_of_ringEquiv (Padic.coefficientExtensionIntegers l E) _
    (integers l E) _ ULift.ringEquiv.symm
    (@PrincipalIdealRing.isNoetherianRing (Padic.coefficientExtensionIntegers l E) _
      ((Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
        (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec).2.2.2.2.2.2.2.2.1)

/-- The residue ring in the published first finite level; the exponent is literally one.
Source: blueprint latest, integral-models Stacks proof, O_E/pi_E
(blueprint: lem-sfb-integral-stacks-residue-comparison). -/
abbrev residueRing := integers l E ⧸ (ideal l E) ^ (0 + 1)

variable (X : Scheme.{u})

/-- Derived residue reduction of a completed-coefficient object, using the canonical
projection and the existing derived extension of scalars.
Source: blueprint latest, integral-models Stacks proof, left finite reduction
(blueprint: lem-sfb-integral-stacks-residue-comparison). -/
abbrev completedReduction (K : D (completedRing l E X)) :=
  (extend (quotientMap l E X true 0)).obj K

/-- Derived residue reduction after the published exact restriction of scalars.
Source: blueprint latest, integral-models Stacks proof, right finite reduction
(blueprint: lem-sfb-integral-stacks-residue-comparison). -/
abbrev restrictedReduction (K : D (completedRing l E X)) :=
  (extend (quotientMap l E X false 0)).obj ((dres (scalarMap l E X)).obj K)

private theorem torAmplitude_iso (A : Type (u + 1)) [CommRing A]
    {K L : D (constant (Scheme.coefficientProEtaleModelTopology.{u, u} X) A)}
    (e : K ≅ L) (a b : ℤ) :
    Scheme.HasCoefficientProEtaleTorAmplitude.{u, u} X A K a b ↔
      Scheme.HasCoefficientProEtaleTorAmplitude.{u, u} X A L a b := by
  constructor
  · rintro ⟨hab, hP⟩
    exact ⟨hab, fun P hP' ⟨f⟩ ↦ hP P hP' ⟨f ≪≫ e.symm⟩⟩
  · rintro ⟨hab, hP⟩
    exact ⟨hab, fun P hP' ⟨f⟩ ↦ hP P hP' ⟨f ≪≫ e⟩⟩

private theorem origin_iff [CompactSpace X] [QuasiSeparatedSpace X]
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    (H : Mod (constant (Scheme.coefficientProEtaleModelTopology.{u, u} X) A)) :
    (∃ F : Mod (constant (Scheme.smallModelComparisonEtaleTopology.{u, u} X) A),
      Scheme.IsCoefficientConstructibleEtaleModule.{u, u} X A F ∧
      Nonempty (H ≅ (constructibleComparisonPullback.{u, u} X A).obj F)) ↔
      Scheme.IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf.{u, u} X A H := by
  obtain ⟨eqv, ⟨η⟩⟩ := (constructibleComparison.{u, u} X A).2.2.1
  constructor
  · rintro ⟨F, hF, ⟨f⟩⟩
    let F' : Scheme.CoefficientConstructibleEtaleModuleCategory.{u, u} X A := ⟨F, hF⟩
    exact coefficientProEtale_constructible_of_iso.{u, u} X A
      (η.app F' ≪≫ f.symm) (eqv.functor.obj F').property
  · intro hH
    let H' : ObjectProperty.FullSubcategory
        (Scheme.IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf.{u, u} X A) :=
      ⟨H, hH⟩
    let F' := eqv.inverse.obj H'
    refine ⟨F'.obj, F'.property, ?_⟩
    exact ⟨((ObjectProperty.ι _).mapIso (eqv.counitIso.app H')).symm ≪≫ η.app F'⟩

private theorem residue_maximal : (ideal l E ^ (0 + 1)).IsMaximal := by
  rw [pow_one]
  have h := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
  have hmax : (Padic.coefficientExtensionMaximalIdeal l E).IsMaximal := h.2.2.2.2.1
  have hgen : Ideal.span {Padic.coefficientExtensionUniformizer l E} =
      Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hm : (Ideal.span {Padic.coefficientExtensionUniformizer l E}).IsMaximal := by
    rw [hgen]
    exact hmax
  have hm' := hm.map_bijective (ULift.ringEquiv.symm :
    Padic.coefficientExtensionIntegers l E ≃+* integers l E)
    ULift.ringEquiv.symm.bijective
  simpa [ideal, Ideal.map_span, Set.image_singleton, ULift.ringEquiv] using hm'

/-- Restriction of integral scalars has canonically identical residue reductions, and
preserves exactly the residue Tor and constructibility conditions in the node.
The first clause describes the canonical derived isomorphism, uniformly in K, by the
ordinary pure-tensor comparison and the flat-term K-flat computation square.

Source: blueprint latest, sec-six-functors-basics/sk-lem-integral-models,
`sk-lem-integral-models-stacks.proof.md`, finite-reduction and field-Tor paragraphs
(blueprint: lem-sfb-integral-stacks-residue-comparison).

Proof:
1. Apply the finite-level clause of integral_constant_completion at index zero.
It supplies the ordinary pure-tensor comparison and the derived natural isomorphism,
including the computation square on flat-term K-flat representatives.
2. Compose the representative isomorphisms in the universal Tor-amplitude test with
this derived isomorphism or its inverse. This transports every fixed Tor interval,
and hence finite Tor amplitude. Applying each cohomology functor transports an
isomorphism to the pullback of a constructible etale module, with the same module.
3. The module equivalence in constructibleComparison identifies constructible
pro-etale modules with modules of constructible etale origin. Its counit gives the
antecedent, and coefficientProEtale_constructible_of_iso transfers constructibility.
The locally Noetherian hypothesis supplies quasi-separatedness of X.
4. The recorded DVR has maximal ideal generated by the recorded uniformizer.
Transport this maximality through ULift to give the residue quotient its field
structure. constant_field_finite_tor_amplitude_iff now identifies finite residue Tor
amplitude with bounded cohomology. Combine this criterion, step 2 and step 3 with
the definition of coefficientBoundedConstructibleProEtale. -/
theorem integral_stacks_residue_comparison [CompactSpace X] [IsLocallyNoetherian X] :
    (∃ α : res (scalarMap l E X) ⋙ change (quotientMap l E X false 0) ≅
        change (quotientMap l E X true 0),
      (∀ (M : Mod (completedRing l E X))
        (U : (Scheme.coefficientProEtaleSiteModel.{u, u} X)ᵒᵖ)
        (s : (finiteRing l E X 0).obj.obj U) (m : M.val.obj U),
        (α.hom.app M).val.app U
          (tensorSection (quotientMap l E X false 0)
            ((res (scalarMap l E X)).obj M) U s m) =
          tensorSection (quotientMap l E X true 0) M U s m) ∧
      ∃ β : extend (quotientMap l E X true 0) ≅
          dres (scalarMap l E X) ⋙ extend (quotientMap l E X false 0),
        ∀ P : Cx (completedRing l E X), P.IsAcyclicTensorKFlat →
          (∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) →
          (extend (quotientMap l E X false 0)).map
              ((resFactors (scalarMap l E X)).inv.app P) ≫
            (extendComparison (quotientMap l E X false 0)).app
              (((res (scalarMap l E X)).mapHomologicalComplex (.up ℤ)).obj P) ≫
            (Q (finiteRing l E X 0)).map
              ((NatIso.mapHomologicalComplex α (.up ℤ)).hom.app P) =
          β.inv.app ((Q (completedRing l E X)).obj P) ≫
            (extendComparison (quotientMap l E X true 0)).app P) ∧
    (∀ (K : D (completedRing l E X)) (a b : ℤ),
      (Scheme.HasCoefficientProEtaleTorAmplitude.{u, u} X (residueRing l E)
          (completedReduction l E X K) a b ∧
        ∀ i : ℤ, ∃ F : Mod (constant
            (Scheme.smallModelComparisonEtaleTopology.{u, u} X) (residueRing l E)),
          Scheme.IsCoefficientConstructibleEtaleModule.{u, u} X (residueRing l E) F ∧
          Nonempty ((coefficientModelCohomology (finiteRing l E X 0) i).obj
              (completedReduction l E X K) ≅
            (constructibleComparisonPullback.{u, u} X (residueRing l E)).obj F)) ↔
      (Scheme.HasCoefficientProEtaleTorAmplitude.{u, u} X (residueRing l E)
          (restrictedReduction l E X K) a b ∧
        ∀ i : ℤ, ∃ F : Mod (constant
            (Scheme.smallModelComparisonEtaleTopology.{u, u} X) (residueRing l E)),
          Scheme.IsCoefficientConstructibleEtaleModule.{u, u} X (residueRing l E) F ∧
          Nonempty ((coefficientModelCohomology (finiteRing l E X 0) i).obj
              (restrictedReduction l E X K) ≅
            (constructibleComparisonPullback.{u, u} X (residueRing l E)).obj F))) ∧
    (∀ K : D (completedRing l E X),
      (coefficientBoundedConstructibleProEtale.{u, u} X (residueRing l E)
          (completedReduction l E X K) ∧
        Scheme.HasFiniteCoefficientProEtaleTorAmplitude.{u, u} X (residueRing l E)
          (completedReduction l E X K)) ↔
      (Scheme.HasFiniteCoefficientProEtaleTorAmplitude.{u, u} X (residueRing l E)
          (restrictedReduction l E X K) ∧
        ∀ i : ℤ, ∃ F : Mod (constant
            (Scheme.smallModelComparisonEtaleTopology.{u, u} X) (residueRing l E)),
          Scheme.IsCoefficientConstructibleEtaleModule.{u, u} X (residueRing l E) F ∧
          Nonempty ((coefficientModelCohomology (finiteRing l E X 0) i).obj
              (restrictedReduction l E X K) ≅
            (constructibleComparisonPullback.{u, u} X (residueRing l E)).obj F))) ∧
    (∀ M : D (finiteRing l E X 0),
      Scheme.HasFiniteCoefficientProEtaleTorAmplitude.{u, u} X (residueRing l E) M ↔
        ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, i < a ∨ b < i →
          IsZero ((coefficientModelCohomology (finiteRing l E X 0) i).obj M)) := by
  have : (ideal l E ^ (0 + 1)).IsMaximal := residue_maximal l E
  let : Field (residueRing l E) := Ideal.Quotient.field _
  have hfield (M : D (finiteRing l E X 0)) :=
    Scheme.constant_field_finite_tor_amplitude_iff.{u, u} X (residueRing l E) M
  obtain ⟨α, hα, β, hβ⟩ :=
    (IntegralConstantCompletion.integral_constant_completion l E X).2.2.2 0
  have htor (K : D (completedRing l E X)) (a b : ℤ) :
      Scheme.HasCoefficientProEtaleTorAmplitude.{u, u} X (residueRing l E)
        (completedReduction l E X K) a b ↔
      Scheme.HasCoefficientProEtaleTorAmplitude.{u, u} X (residueRing l E)
        (restrictedReduction l E X K) a b :=
    torAmplitude_iso X (residueRing l E) (β.app K) a b
  have hfinite (K : D (completedRing l E X)) :
      Scheme.HasFiniteCoefficientProEtaleTorAmplitude.{u, u} X (residueRing l E)
        (completedReduction l E X K) ↔
      Scheme.HasFiniteCoefficientProEtaleTorAmplitude.{u, u} X (residueRing l E)
        (restrictedReduction l E X K) :=
    exists_congr fun a ↦ exists_congr fun b ↦ htor K a b
  have horigin (K : D (completedRing l E X)) :
      (∀ i : ℤ, ∃ F : Mod (constant
          (Scheme.smallModelComparisonEtaleTopology.{u, u} X) (residueRing l E)),
        Scheme.IsCoefficientConstructibleEtaleModule.{u, u} X (residueRing l E) F ∧
        Nonempty ((coefficientModelCohomology (finiteRing l E X 0) i).obj
            (completedReduction l E X K) ≅
          (constructibleComparisonPullback.{u, u} X (residueRing l E)).obj F)) ↔
      (∀ i : ℤ, ∃ F : Mod (constant
          (Scheme.smallModelComparisonEtaleTopology.{u, u} X) (residueRing l E)),
        Scheme.IsCoefficientConstructibleEtaleModule.{u, u} X (residueRing l E) F ∧
        Nonempty ((coefficientModelCohomology (finiteRing l E X 0) i).obj
            (restrictedReduction l E X K) ≅
          (constructibleComparisonPullback.{u, u} X (residueRing l E)).obj F)) := by
    apply forall_congr'
    intro i
    constructor
    · rintro ⟨F, hF, ⟨f⟩⟩
      exact ⟨F, hF, ⟨(coefficientModelCohomology _ i).mapIso (β.app K).symm ≪≫ f⟩⟩
    · rintro ⟨F, hF, ⟨f⟩⟩
      exact ⟨F, hF, ⟨(coefficientModelCohomology _ i).mapIso (β.app K) ≪≫ f⟩⟩
  refine ⟨⟨α, hα, β, hβ⟩, ?_, ?_, hfield⟩
  · intro K a b
    exact and_congr (htor K a b) (horigin K)
  · intro K
    constructor
    · rintro ⟨hC, hT⟩
      refine ⟨(hfinite K).mp hT, (horigin K).mp ?_⟩
      intro i
      exact (origin_iff X (residueRing l E) _).mpr (hC.1 i)
    · rintro ⟨hT, hC⟩
      have hT' := (hfinite K).mpr hT
      refine ⟨⟨?_, (hfield _).mp hT'⟩, hT'⟩
      intro i
      exact (origin_iff X (residueRing l E) _).mp ((horigin K).mpr hC i)

end AlgebraicGeometry.ProEtale.IntegralStacksResidueComparison
