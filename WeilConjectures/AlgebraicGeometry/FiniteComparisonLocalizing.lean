/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteComparisonCoefficientsSupplement
public import WeilConjectures.AlgebraicGeometry.LocalizingClosure
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteCondensedRing
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteSchemeRingSupplement
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.AlgebraicGeometry.UnboundedDirectImageComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact
import WeilConjectures.AlgebraicGeometry.ProEtaleDirectImageComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleExtensionZeroComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian
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
import WeilConjectures.AlgebraicGeometry.ProEtaleClassicalSheavesModules
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Topology.Defs.Filter
import WeilConjectures.AlgebraicGeometry.CoefficientTorFlatModelSupplement
import WeilConjectures.AlgebraicGeometry.ConstructibleComparisonFlatPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.ContinuousRingedToposModuleDirectImage
import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
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
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIsoSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.AlgebraicGeometry.ConstructibleComparisonTensorTestReflection
import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorComparisonConstruction
import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorComparisonData
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import WeilConjectures.AlgebraicGeometry.RingedTopoiInverseImageTensorComparison
import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections
import WeilConjectures.AlgebraicGeometry.RingedTopoiInverseImageTensorPairingIsIso
import WeilConjectures.AlgebraicGeometry.RingedTopoiInverseImagePairing
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import WeilConjectures.AlgebraicGeometry.RingedTopoiScalarTensorComparison
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.AlgebraicGeometry.UnboundedSiteComparison
import WeilConjectures.AlgebraicGeometry.LocalizingAdmissibleCoefficients
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Mathlib.CategoryTheory.Limits.FullSubcategory
import WeilConjectures.AlgebraicGeometry.FiniteComparisonPresentationSupplement
import WeilConjectures.AlgebraicGeometry.FiniteComparisonFaithful

/-!
# Finite coefficient comparison on localizing closures

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-ctf-finite-comparison/
sk-prop-ctf-finite-comparison-localizing.md
(blueprint: det-ctf-finite-comparison-localizing).

## Main definitions

* `finiteComparisonRealization`: the specified finite-discrete coefficient transport.
* `finiteComparisonEtaleClosure`, `finiteComparisonProEtaleClosure`: the two closures.
* `finiteComparisonOpenIso`, `finiteComparisonCompactSupportMap`: the canonical arrows.

## Main statements

* `finiteComparisonRealization_exact`: exactness of the specified coefficient transport.
* `finiteComparisonLocalizing`: the equivalence and its compatibility with operations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj TensorProduct ZeroObject

section LocalizingArgument
universe w v₁ v₂
namespace CategoryTheory

variable {C : Type w} {D : Type w} [Category.{v₁} C] [Category.{v₂} D]
  [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

private theorem closureLocalizing (S : ObjectProperty C) :
    IsLocalizingSubcategory (localizingClosure S) := by
  have hiso : (localizingClosure S).IsClosedUnderIsomorphisms := by
    constructor
    intro K L e hK P hP hS
    let := hP.2.1
    exact P.prop_of_iso e (hK P hP hS)
  let := hiso
  have hzero : (localizingClosure S).ContainsZero := by
    refine ⟨0, isZero_zero _, ?_⟩
    intro P hP hS
    let := hP.1
    let := hP.2.1
    exact P.prop_zero
  let := hzero
  have hshift : (localizingClosure S).IsStableUnderShift ℤ := by
    constructor
    intro n
    constructor
    intro K hK
    rw [ObjectProperty.prop_shift_iff]
    intro P hP hS
    let := hP.1
    exact P.le_shift n K (hK P hP hS)
  let := hshift
  have htri : (localizingClosure S).IsTriangulated := by
    refine { ext₂' := ?_ }
    intro T hT h₁ h₃
    apply ObjectProperty.le_isoClosure
    intro P hP hS
    let := hP.1
    let := hP.2.1
    exact P.ext_of_isTriangulatedClosed₂ T hT (h₁ P hP hS) (h₃ P hP hS)
  refine ⟨htri, hiso, ?_⟩
  intro I F hF hK
  change ∀ P, IsLocalizingSubcategory P → (∀ K, S K → P K) → _
  intro P hP hS
  exact hP.2.2 F hF (fun i ↦ hK i P hP hS)

private theorem inverseImageLocalizing (P : ObjectProperty D) (F : C ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated]
    [∀ I : Type w, PreservesColimitsOfShape (Discrete I) F]
    (hP : IsLocalizingSubcategory P) :
    IsLocalizingSubcategory (P.inverseImage F) := by
  let := hP.1
  let := hP.2.1
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro I G hG hPG
  let := hG
  let : HasColimit (G ⋙ F) := ⟨_, isColimitOfPreserves F (colimit.isColimit G)⟩
  exact P.prop_of_iso (preservesColimitIso F G).symm
    (hP.2.2 (G ⋙ F) inferInstance hPG)

private theorem imageLocalizing (P : ObjectProperty C) (F : C ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated]
    [Coreflective F] (hP : IsLocalizingSubcategory P) :
    IsLocalizingSubcategory (P.map F) := by
  let := hP.1
  let := hP.2.1
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro I H hH hPH
  let := hH
  have hHF (j : Discrete I) : F.essImage (H.obj j) := by
    obtain ⟨K, _, e⟩ := hPH j.as
    exact ⟨K, e⟩
  let G := Functor.essImage.liftFunctor H F hHF
  let e := Functor.essImage.liftFunctorCompIso H F hHF
  let : HasColimit (G ⋙ F) := hasColimit_of_iso e
  let : HasColimit G := hasColimit_of_coreflective G F
  have hPG (i : I) : P (G.obj (Discrete.mk i)) := by
    obtain ⟨K, hK, ⟨iK⟩⟩ := hPH i
    exact P.prop_of_iso (F.preimageIso (iK ≪≫ (e.app (Discrete.mk i)).symm)) hK
  refine ⟨colimit G, hP.2.2 G inferInstance hPG, ⟨?_⟩⟩
  exact (preservesColimitIso F G) ≪≫ HasColimit.isoOfNatIso e


private theorem closureEquivalence (S : ObjectProperty C) (T : ObjectProperty D) (F : C ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated] [Coreflective F]
    (hS : ∀ K, S K → localizingClosure T (F.obj K))
    (hT : ∀ K, T K → (localizingClosure S).map F K) :
    ∃ hpres : ∀ K, localizingClosure S K → localizingClosure T (F.obj K),
      ((localizingClosure T).lift ((localizingClosure S).ι ⋙ F)
        (fun K ↦ hpres K.obj K.property)).IsEquivalence := by
  have hpres (K : C) (hK : localizingClosure S K) :
      localizingClosure T (F.obj K) := by
    exact hK ((localizingClosure T).inverseImage F)
      (inverseImageLocalizing _ _ (closureLocalizing T)) hS
  refine ⟨hpres, ?_⟩
  let H := (localizingClosure T).lift ((localizingClosure S).ι ⋙ F)
    (fun K ↦ hpres K.obj K.property)
  have himage (K : D) (hK : localizingClosure T K) :
      (localizingClosure S).map F K :=
    hK _ (imageLocalizing _ F (closureLocalizing S)) hT
  have : H.EssSurj := by
    constructor
    intro K
    obtain ⟨L, hL, ⟨e⟩⟩ := himage K.obj K.property
    exact ⟨⟨L, hL⟩, ⟨ObjectProperty.isoMk _ e⟩⟩
  exact { }

end CategoryTheory
end LocalizingArgument

namespace AlgebraicGeometry.ProEtale


variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [DiscreteTopology B] [Finite B]
variable (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (coherentTopology Profinite.{u})
  ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} B))) ≅
    Profinite.continuousMapRingObj.{u} B) [IsMonHom eR.hom]

/-- The canonical open-extension comparison, applied termwise and localized.
Source: blueprint finite comparison, Operations; Stacks Tag 09AF
(blueprint: det-ctf-finite-comparison-localizing). -/
def finiteComparisonOpenIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} B)) j).mapDerivedCategory ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) X).mapDerivedCategory ≅
      (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) U).mapDerivedCategory ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} B)) j).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (openImmersionLowerShriekComparisonUpperStarIso
        (ModuleCat.{u + 1} (ULift.{u + 1} B)) j) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- For the chosen open/proper factorization, the compact-support comparison is exactly
alpha at j_! K followed by Rp_* of the open comparison. All values are ambient.
Source: blueprint finite comparison, final paragraph of proof
(blueprint: det-ctf-finite-comparison-localizing). -/
def finiteComparisonCompactSupportMap {X P Y : Scheme.{u}} (j : X ⟶ P) (p : P ⟶ Y)
    [IsOpenImmersion j]
    (K : Etale.DerivedCategoryModule (ULift.{u + 1} B) X) :=
  unboundedDirectImageComparisonMap (ULift.{u + 1} B) p
      ((Etale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1} B)) j).mapDerivedCategory.obj K) ≫
    (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) p).rightDerivedFunctor.map
      ((finiteComparisonOpenIso B j).hom.app K)

/-- The finite-Tor constructible generators correspond under the comparison functor.
Source: blueprint finite comparison, opening paragraph
(blueprint: lem-ctf-finite-comparison-generators).

Proof: apply the finite Noetherian coefficient comparison to the coefficient-sized small
site models, then transport its restricted equivalence through the constant-scalar
presentations, site equivalences, and the specified finite discrete scheme-ring
isomorphism. These transports preserve constructibility, finite Tor amplitude, and the
ambient derived comparison, yielding both generator inclusions. The empty scheme and
zero ring are included by the same equivalence argument. -/
theorem finiteComparisonGenerators_identification (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] :
    (∀ K : Etale.DerivedCategoryModule (ULift.{u + 1} B) X,
      finiteComparisonEtaleGenerators B X K →
        finiteComparisonProEtaleGenerators B eR X
          ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B))
            X).mapDerivedCategory.obj K)) ∧
    (∀ K : _root_.DerivedCategory
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} B))),
      finiteComparisonProEtaleGenerators B eR X K →
        (finiteComparisonEtaleGenerators B X).map
          (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B))
            X).mapDerivedCategory K) := by
  let A := ULift.{u + 1} B
  let : IsNoetherianRing A := inferInstance
  let : HasDerivedCategory.{u + 2} (ConstantCompletion.Mod (ConstantCompletion.constant
      (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} X) A)) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory.{u + 2} (ConstantCompletion.Mod (ConstantCompletion.constant
      (Scheme.coefficientProEtaleModelTopology.{u, u + 1} X) A)) :=
    HasDerivedCategory.standard _
  let E := (finiteComparisonEtaleModelRealization X A).mapDerivedCategory
  let G := (finiteComparisonProEtaleModelRealization X A).mapDerivedCategory
  let F := (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory
  obtain ⟨D, hD, _, H, ⟨hH⟩⟩ := finiteTorComparisonNoetherian.{u, u + 1} X A
  obtain ⟨hE, hG⟩ := finiteComparisonPresentation B X eR
  obtain ⟨esquare⟩ := finiteComparisonModelDerivedSquare X A D hD
  constructor
  · intro K hK
    rw [← hE] at hK
    obtain ⟨L, hL, ⟨eL⟩⟩ := hK
    rw [← hG]
    let L' := H.functor.obj ⟨L, hL⟩
    refine ⟨L'.obj, L'.property, ⟨?_⟩⟩
    exact G.mapIso (hH.app ⟨L, hL⟩) ≪≫
      (esquare.app L).symm ≪≫ F.mapIso eL
  · intro K hK
    rw [← hG] at hK
    obtain ⟨M, hM, ⟨eM⟩⟩ := hK
    let M' := H.inverse.obj ⟨M, hM⟩
    refine ⟨E.obj M'.obj, ?_, ⟨?_⟩⟩
    · rw [← hE]
      exact ⟨M'.obj, M'.property, ⟨Iso.refl _⟩⟩
    · exact esquare.app M'.obj ≪≫ G.mapIso (hH.app M').symm ≪≫
        G.mapIso (ObjectProperty.ι _ |>.mapIso (H.counitIso.app ⟨M, hM⟩)) ≪≫ eM

/-- Comparison identifies the two localizing closures, exactly and with ambient sums,
and the canonical pullback, direct-image, open-extension and compact-support comparisons
are invertible on the indicated inputs. No stability assertion for direct images occurs.

Source: blueprint main-20261015, sk-prop-ctf-finite-comparison-localizing.md and its proof
(blueprint: det-ctf-finite-comparison-localizing).

Proof, following the node's five steps:
1. The finite-discrete condensed-ring and scheme-ring identifications transport module
   actions exactly, preserving sums, tensor and the finite constant models. The unbounded
   site comparison is exact, fully faithful and sum-preserving
   (lem-sfb-unbounded-site-comparison). The finite Noetherian coefficient comparison
   det-pe-finite-tor-comparison-noetherian identifies the Dctf generators.
2. The inverse image of the pro-etale closure is replete, triangulated and sum-closed.
   It contains the etale generators, so the defining intersection of
   sk-def-localizing-closure gives preservation of the etale closure.
3. The replete essential image of that closure is sum-closed and shift-closed.
   Fullness lifts any arrow between image objects, and exactness sends its cone to
   a cone of the given arrow. Thus the essential image is triangulated, including zero
   from the empty sum. It contains all pro-etale generators by step 1. Minimality gives
   the reverse inclusion. Full faithfulness restricts, giving the equivalence; triangles
   and sums are the ambient ones.
4. The pullback square is sk-thm-pe-direct-image-comparison. For open extension use
   lem-cbc-proetale-extension-zero-comparison and the two extension-exactness nodes:
   applying the sheaf isomorphism degreewise gives a natural complex isomorphism and
   exactness descends it through quasi-isomorphisms. For finite-type direct image use
   lem-sfb-unbounded-direct-image-comparison. Restrict these ambient maps to closure inputs.
5. For a chosen compactification compose alpha on j_! K with Rp_* of the open
   comparison. Both factors are isomorphisms in the ambient category, naturally in K.
   Their composite is exactly the stipulated comparison for Rf_! = Rp_* j_!; no closure
   stability of direct image is used. -/
theorem finiteComparisonLocalizing
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k]
    [Algebra (ZMod p) k] [IsAlgClosure (ZMod p) k]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ p)
    (hB : ∃ n : ℕ, (ℓ : B) ^ n = 0)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))] :
    ∃ hpres : ∀ K : Etale.DerivedCategoryModule (ULift.{u + 1} B) X,
        finiteComparisonEtaleClosure B X K →
          finiteComparisonProEtaleClosure B eR X
            ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B))
              X).mapDerivedCategory.obj K),
      ((finiteComparisonProEtaleClosure B eR X).lift
        ((finiteComparisonEtaleClosure B X).ι ⋙
          (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) X).mapDerivedCategory)
        (fun K ↦ hpres K.obj K.property)).IsEquivalence ∧
      (∀ T : Triangle (Etale.DerivedCategoryModule (ULift.{u + 1} B) X),
        finiteComparisonEtaleClosure B X T.obj₁ →
        finiteComparisonEtaleClosure B X T.obj₂ →
        finiteComparisonEtaleClosure B X T.obj₃ →
        T ∈ distTriang _ →
        ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B))
          X).mapDerivedCategory.mapTriangle.obj T) ∈ distTriang _) ∧
      (∀ (I : Type (u + 2)) (K : I → Etale.DerivedCategoryModule (ULift.{u + 1} B) X),
        (∀ i : I, finiteComparisonEtaleClosure B X (K i)) →
        ∀ c : Cofan K, IsColimit c → finiteComparisonEtaleClosure B X c.pt ∧
          Nonempty (IsColimit
            ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B))
              X).mapDerivedCategory.mapCocone c))) ∧
      (∀ (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
        [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
        (g : X ⟶ Y) [g.IsOver (Spec (.of k))] [LocallyOfFiniteType g] [QuasiCompact g],
        (∀ K : Etale.DerivedCategoryModule (ULift.{u + 1} B) Y,
          finiteComparisonEtaleClosure B Y K →
          IsIso ((unboundedDirectImagePullbackIso (ULift.{u + 1} B) g).hom.app K)) ∧
        (∀ K : Etale.DerivedCategoryModule (ULift.{u + 1} B) X,
          finiteComparisonEtaleClosure B X K →
          IsIso (unboundedDirectImageComparisonMap (ULift.{u + 1} B) g K))) ∧
      (∀ (U : Scheme.{u}) [U.Over (Spec (.of k))]
        [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
        (j : U ⟶ X) [j.IsOver (Spec (.of k))] [IsOpenImmersion j]
        (K : Etale.DerivedCategoryModule (ULift.{u + 1} B) U),
        finiteComparisonEtaleClosure B U K → IsIso ((finiteComparisonOpenIso B j).hom.app K)) ∧
      (∀ (P Y : Scheme.{u}) [P.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
        [LocallyOfFiniteType (P ↘ Spec (.of k))] [QuasiCompact (P ↘ Spec (.of k))]
        [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
        (j : X ⟶ P) (r : P ⟶ Y) [j.IsOver (Spec (.of k))] [r.IsOver (Spec (.of k))]
        [IsOpenImmersion j] [IsProper r]
        (K : Etale.DerivedCategoryModule (ULift.{u + 1} B) X),
        finiteComparisonEtaleClosure B X K →
          IsIso (finiteComparisonCompactSupportMap B j r K)) := by
  let A : Type (u + 1) := ULift.{u + 1} B
  have hA : ∃ n : ℕ, (ℓ : A) ^ n = 0 := by
    obtain ⟨n, hn⟩ := hB
    exact ⟨n, ULift.ext _ _ hn⟩
  let : CharP k p :=
    charP_of_injective_algebraMap (RingHom.injective (algebraMap (ZMod p) k)) p
  have hunit : IsUnit (algebraMap ℤ k (ℓ : ℤ)) := by
    rw [map_natCast, isUnit_iff_ne_zero]
    change (ℓ : k) ≠ 0
    intro hzero
    exact hℓ ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).mp
      ((CharP.cast_eq_zero_iff k p ℓ).mp hzero)).symm
  let : IsAlgClosed k := IsAlgClosure.isAlgClosed (ZMod p)
  let : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  let : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  let F := (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory
  obtain ⟨hFF⟩ := finiteComparisonOrdinary_fullyFaithful A k
    (Or.inr inferInstance) hunit hA X
  let : F.Full := hFF.full
  let : F.Faithful := hFF.faithful
  let adj := (comparisonAdjunction (ModuleCat.{u + 1} A) X)
    |>.mapDerivedCategoryRightDerivedAdjunction
  let : Coreflective F := { R := _, adj := adj }
  obtain ⟨hgen, hgen'⟩ := finiteComparisonGenerators_identification B eR X
  obtain ⟨hpres, hequiv⟩ := closureEquivalence
    (finiteComparisonEtaleGenerators B X) (finiteComparisonProEtaleGenerators B eR X) F
    (fun K hK P _ hP ↦ hP _ (hgen K hK))
    (fun K hK ↦ by
      obtain ⟨L, hL, e⟩ := hgen' K hK
      exact ⟨L, fun P _ hP ↦ hP _ hL, e⟩)
  refine ⟨hpres, hequiv, ?_, ?_, ?_, ?_, ?_⟩
  · intro T _ _ _ hT
    exact F.map_distinguished T hT
  · intro I K hK c hc
    let S := finiteComparisonEtaleClosure B X
    have hloc : IsLocalizingSubcategory S := closureLocalizing _
    let := hloc.2.1
    let : HasColimit (Discrete.functor K) := ⟨c, hc⟩
    refine ⟨S.prop_of_iso
      ((colimit.isColimit _).coconePointUniqueUpToIso hc)
      (hloc.2.2 (Discrete.functor K) inferInstance hK), ?_⟩
    exact ⟨isColimitOfPreserves F hc⟩
  · intro Y _ _ _ g _ _ _
    constructor
    · intro K _
      infer_instance
    · intro K _
      exact unboundedDirectImageComparison k (Or.inr inferInstance) hunit A hA g K
  · intro U _ _ _ j _ _ K _
    infer_instance
  · intro P Y _ _ _ _ _ _ j r _ _ _ _ K _
    unfold finiteComparisonCompactSupportMap
    have := unboundedDirectImageComparison k (Or.inr inferInstance) hunit A hA r
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj K)
    infer_instance

end AlgebraicGeometry.ProEtale
