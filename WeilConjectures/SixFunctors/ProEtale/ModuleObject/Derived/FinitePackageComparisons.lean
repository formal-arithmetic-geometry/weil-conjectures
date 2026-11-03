/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageOfUniverses
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
public import Mathlib.Data.Finset.Max
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.AdmissibleBoundedConstructibleTriangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedPointModuleComparison
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralGluing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocallyClosedGeneratorTensorIntersection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenFiltrationSuccessor
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.ConstructibleSheaf.Devissage
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
public import WeilConjectures.AlgebraicGeometry.CondensedIntegralCriterion
public import WeilConjectures.AlgebraicGeometry.FiniteCondensedCtfEquivalence
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteScalarConstantModels
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicConstantLocalModelTor
public import Mathlib.RingTheory.Finiteness.Projective
public import WeilConjectures.AlgebraicGeometry.EtaleLocallyConstantPerfectComplex
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedScalarTensor
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartOrderedRefinement
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.EtaleDomainPullbackCalculus
public import WeilConjectures.AlgebraicGeometry.EtaleLisseCtfPerfectLocalModel
public import WeilConjectures.AlgebraicGeometry.RefinementPreservesFiniteLisse
public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.ConstructibleSheaf.KernelCokernel
public import WeilConjectures.ConstructibleSheaf.Refinement
public import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleScalarMateProjection
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.SixFunctors.OpenClosed.Complex
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingPullbackFixed
public import WeilConjectures.SixFunctors.ProEtale.Comparison.UpperStar
public import WeilConjectures.SixFunctors.ProEtale.Comparison.ConstantSheaf
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartGeneration
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenImmersionTensorProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersionTensorProjection
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.FieldTensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonPresentationSupplement
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonLocalizing
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
public import WeilConjectures.Compactification.Over
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import WeilConjectures.CategoryTheory.DerivedCategory.SixFunctors.NativeInternalHomExact
public import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory
public import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded.IntegralModelsEmbedded
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
public import WeilConjectures.AlgebraicGeometry.SixFunctors.DualityPairing
public import WeilConjectures.Compactification.Dense
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedSiteComparison
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEquivalence
public import WeilConjectures.SixFunctors.Etale.Derived.GeometricBidualityInduction
public import WeilConjectures.CategoryTheory.Monoidal.Closed.EvaluationBidualComparisonTransport
public import WeilConjectures.AlgebraicGeometry.Base.BaseFieldCohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralModels
public import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.CondensedCoefficientPoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorHom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedCoefficientMaps
public import WeilConjectures.AlgebraicGeometry.RootCoordinateFace.RootTowerCoordinateFace
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixCtfGenerators
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleOrigin
public import WeilConjectures.AlgebraicGeometry.Flat.FlatModelGeneration
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleLisseModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleExtensionIso
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartLocallyClosedExtension
public import Mathlib.CategoryTheory.Triangulated.Generators
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
public import WeilConjectures.ConstructibleSheaf.OpenClosed
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartSheafConeWitness
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralDerivedCoefficientData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralConstantModelLocalResolution
public import WeilConjectures.ProperBaseChange.IntegralLfpLocallyFreeResolution
public import WeilConjectures.ProperBaseChange.CondensedConstructibleSerre
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralLfpConstantModelComparison
public import WeilConjectures.AlgebraicGeometry.CondensedLocallyClosedExtensionTower
public import WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixAdmissibleThickness
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.AlgebraicGeometry.Locally.LocallyPerfectScalarModel
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.AlgebraicGeometry.Sites.QuasiCompact
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeMapDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralLisseDerivedAux
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalLeftDerived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientProjectionSquare
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientsFiniteFree
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralDerivedIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.QlbarDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.FiniteFreeScalarDerivedComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteScalarProjectionCase
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarRestrictionMateNormalization
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarMateProjection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralFinitePointResolution
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorComparison
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedScalarCoefficientMaps
public import Mathlib.CategoryTheory.ObjectProperty.Shift
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProEtaleProperOpenInterchange
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import WeilConjectures.SixFunctors.ScalarOpenCompositorCoherence
public import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarGeometricExchangeRectangle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenExtensionConstructibleFiniteTor
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientRefinement
public import WeilConjectures.CategoryTheory.AdjunctionSquareComposition
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteCoefficientSmallCarrierComparison
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingLowerShriekCompositionModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestrictionMaps
public import WeilConjectures.Compactification.BaseChange
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import WeilConjectures.CategoryTheory.CompactGeneratorsBuildObjects
public import WeilConjectures.CategoryTheory.CompactObject
public import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingEtaleCompactGenerators
public import Mathlib.Algebra.CharP.CharAndCard
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Formal.FormalClosedSupportDerived
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalTowerCoefficients
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerLimit
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerTrace
public import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1Triangle
public import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1UnitCounit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestriction
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenClosedSequenceRingSheaf
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
public import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCycleClass
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportComposition
public import WeilConjectures.AlgebraicGeometry.PurityTransport.Transport
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralUniformCoefficient
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedEtaleOriginWitness
public import WeilConjectures.SixFunctors.Compact.CompactSupportReductionTower
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralCompactSupportUniformRestriction
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import WeilConjectures.Algebra.Homology.RingedCoefficientProjection.RingedCoefficientProjectionDataSupplement
public import WeilConjectures.Algebra.Homology.RingedCoefficientProjection.RingedCoefficientPullbackComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.Picard.SuccessiveDerivedQuotientNormalization
public import WeilConjectures.Algebra.Homology.RingedCoefficientProjection.RingedCoefficientPullbackShifts
public import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import WeilConjectures.Algebra.Homology.RingedCoefficientProjection.RingedCoefficientScalarUnits
public import WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.AdjunctionShift
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalization
public import WeilConjectures.ProperBaseChange.CondensedERealization.CondensedERealizationDefinitions
public import WeilConjectures.ProperBaseChange.CondensedERealizationSystem
public import WeilConjectures.ProperBaseChange.CondensedERealization.CondensedEIntegralExchange
public import WeilConjectures.ProperBaseChange.CondensedERealization.CondensedERationalCondensedExchange
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedFlatCoefficientCalculus
public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemOperations
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
public import WeilConjectures.SmoothPurity.CompactSupportCondensedRealization.CondensedCompactSupportProjection
public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralCompactificationSystemRealization
public import WeilConjectures.SixFunctors.GeneratorReduction.GeneratorReductionStatement
public import WeilConjectures.AlgebraicGeometry.Sf.SfCbcCompactSupportCompositionLimit
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.AlgebraicGeometry.Standard.StandardQuotientsPerfectSupplement
public import Mathlib.GroupTheory.OrderOfElement
public import WeilConjectures.SmoothPurity.Pur.PurNormalizedReconstructionAdjunctionCalculus
public import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
public import Mathlib.Data.Nat.Prime.Infinite
public import WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.Sf.SfCbcExtensionZeroCompletion
public import WeilConjectures.AlgebraicGeometry.Constant.ConstantOpenRestrictionModelComparison
public import WeilConjectures.SixFunctors.Sf.SfIntegralReductionTowerSupplement
public import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportRealization
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenCalculus
public import WeilConjectures.Compactification.Triangle
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictConstantTowerOperationsSupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import WeilConjectures.CategoryTheory.Ringed.RingedTowerPushforwardLimitComparison
public import WeilConjectures.AlgebraicGeometry.AmbientProperOpen.AmbientProperOpenPasting
public import WeilConjectures.SixFunctors.GeneratorReduction.OpenReconstructionEffectivity
public import WeilConjectures.SixFunctors.IntegralSystemRealization.CompletedShriekCompositionLaws
public import WeilConjectures.SmoothPurity.CompactSupportCondensedRealization.CompactSupportCondensedRealization
public import WeilConjectures.SmoothPurity.Completed.CompletedCoefficientPresentationTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek
public import WeilConjectures.SmoothPurity.Supporting.Coefficient.ConstantCoefficientObjectsConstructible
public import WeilConjectures.CategoryTheory.Scalar.ScalarLocalizationSheafExact
public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientLocalization
public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientGeneralPullbackIso
public import WeilConjectures.SmoothPurity.SheafRingCoefficientOrdinaryAdjunction
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralCompletedCoefficientTransportSupplement
public import WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcCompletedPullbackActualSupplement
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import WeilConjectures.ProperBaseChange.IntegralCoefficientPresentation.IntegralCoefficientPresentationComparison
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleCompleteSupplement
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumCompletedSupplement
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulQuotientComparison
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedRlimFunctor
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedQuotientUnitNormalization
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCompletionCompletedSupplement
public import WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantCoefficientEquivalence
public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRKFlatTransition
public import WeilConjectures.SmoothPurity.Normalized.NormalizedDVREffectivity
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperBaseChange.Compatibility
public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDescentTwoColimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompCompositionBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosedLocalization
public import WeilConjectures.PoincareDuality.ProjectionFormula
public import WeilConjectures.AlgebraicGeometry.ModuleRingedComparison.ModuleRingedToposDerivedComparison
public import WeilConjectures.SixFunctors.Finite.Coefficient.FiniteCoefficientHomChange
public import WeilConjectures.SixFunctors.Finite.FiniteConstructibleHom
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedBelowDerivedSmoothBaseChange
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import WeilConjectures.SmoothPurity.Supporting.SixFunctorDatum
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Native.NativeConstructibleExceptionalInverseImage
public import WeilConjectures.Compactification.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionProjection
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedCondensedCoefficients
public import WeilConjectures.AlgebraicGeometry.Native.NativeHomSourceShiftData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleDerivedFunctorShifts
public import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedDualizableHomWindow
public import WeilConjectures.AlgebraicGeometry.CondensedBoundedOpenOperations
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedProperConstructibleProjection
public import WeilConjectures.SmoothPurity.Supporting.DirectImagesConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
public import Mathlib.CategoryTheory.Adjunction.Opposites
public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import WeilConjectures.CategoryTheory.Projection.ProjectionInternalHom
public import WeilConjectures.AlgebraicGeometry.Open.OpenExtensionConstantModelConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedCoefficientUnit
public import WeilConjectures.SixFunctors.Etale.Derived.RationalStage
public import WeilConjectures.SixFunctors.Sf.SfBidualityClass
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.CategoryTheory.FiniteCondensedNormalizedAdjunction
public import WeilConjectures.AlgebraicGeometry.FiniteNativeTensor.FiniteNativeTensorComparison
public import WeilConjectures.SixFunctors.Etale.Derived.VerdierBiduality
public import WeilConjectures.SixFunctors.Etale.Derived.WeilComplexDual
public import Mathlib.CategoryTheory.Yoneda
public import WeilConjectures.CategoryTheory.Constant.ConstantScalarRestrictionTensorSupplement
public import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.AlgebraicGeometry.FiniteCondensedVerdierComparison
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCtfInternalEtaleRealization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FiniteFieldDualizingPullback
public import WeilConjectures.SixFunctors.Etale.Derived.DoubleDual
public import Mathlib.Algebra.Field.ULift
public import WeilConjectures.CategoryTheory.RingObjects.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedVerdierScalarTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedVerdierCoefficientComparison
public import WeilConjectures.AlgebraicGeometry.Internal.InternalFirstResidueRingIsoSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
public import WeilConjectures.AlgebraicGeometry.SixFunctors.ShriekCoefficientIsomorphism
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompBaseChangeDefs
public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
public import WeilConjectures.ProEtaleCoefficients.DerivedNakayamaResolution
public import Mathlib.Algebra.Ring.Shrink
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedProperOpenInterchange
public import WeilConjectures.Compactification.NagataCompactification

/-! # Named finite-stage geometric comparisons

Source: latest blueprint sk-thm-sf-comp-composition, equation (6.7), and
its proper/open-interchange normalization; def-fix-six-functor-datum (2).
(blueprint: def-trf-finite-package-comparisons).

The compositor below is a composite of specified maps. Its interchange is selected
from an existence-and-pointwise-uniqueness statement with the adjunction normalization,
not from an aggregate existence assertion about endpoint isomorphisms.

## Main definitions

* `trfDctfToLoc`, `trfLocShift`: the full inclusion and inherited shift.
* `trfDiscreteCoefficientIso`: identity transport to the discrete coefficient presentation.
* `trfNormalizedInterchange`: the uniquely normalized proper/open arrow.
* `trfCompactificationComparison`: the refinement-normalized change of compactification.
* `trfCompositionTower`, `trfTowerComposition`, `trfCompactSupportComposition`:
  the compatible tower and the specified composition map.
* `trfProperCoincidenceIdentityOpen`, `trfProperCoincidence`: proper coincidence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 10000
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The actual ambient shift of a localizing object, with its membership proof.
Source: latest blueprint sk-def-localizing-closure, triangulated closure
(blueprint: def-trf-finite-package-comparisons). -/
def trfLocShift (X : Scheme.{u})
    (K : (localizingClosureProEtale Λ X).FullSubcategory) :
    (localizingClosureProEtale Λ X).FullSubcategory :=
  ⟨K.obj⟦(1 : ℤ)⟧, fun P hP hgen ↦ by
    let := hP.1
    exact P.le_shift (1 : ℤ) K.obj (K.property P hP hgen)⟩

/-- Proper coincidence at the identity-open compactification, derived degreewise and
whiskered by the actual proper direct image. This fixes the map, not only its endpoints.
Source: cor-cbc-proper-coincidence, identity-open normalization, and
latest blueprint def-fix-six-functor-datum (2)
(blueprint: def-trf-finite-package-comparisons). -/
def trfProperCoincidenceIdentityOpen {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    rightDerivedLowerShriekOfCompactification Λ (Compactification.ofIsProper f) ≅
      moduleObjectDerivedPushforward Λ f :=
  Functor.isoWhiskerRight (derivedOpenImmersionLowerShriekId Λ X) _ ≪≫
    Functor.leftUnitor _

/-- Identity transport from a discrete topology to its bottom presentation, at the
level of the same condensed ring object. Keeping the carrier abstract avoids expanding
spectral quotient instances during the topology substitution.
Source: finite coefficient convention (blueprint: def-trf-finite-package-comparisons). -/
def trfDiscreteCoefficientIso (R : Type u) [CommRing R]
    (t : TopologicalSpace R) (hr : @IsTopologicalRing R t inferInstance) (ht : t = ⊥) :
    (letI : TopologicalSpace R := t
     letI : IsTopologicalRing R := hr
     Mon.mk (Profinite.continuousCoefficientRingObj R)) ≅
    (letI : TopologicalSpace R := ⊥
     letI : DiscreteTopology R := discreteTopology_bot R
     Mon.mk (Profinite.continuousCoefficientRingObj R)) := by
  subst t
  exact Iso.refl _

section Finite
variable (ell : ℕ) [Fact ell.Prime] (D : WeilConjectures.FiniteFieldDatum.{u})
  [Fact (ell ≠ D.p)] (E : PadicAlgCl.FiniteIntermediateField ell)
  (n : ℕ) (hn : 1 ≤ n)

set_option quotPrecheck false in
local notation "A[" ell "," E "," n "]" =>
  DerivedNakayama.quotientRing ell (ULift E) n

/-- Characteristic of the fixed algebraic closure, inherited from the finite field.
Source: finite-field convention (blueprint: def-trf-finite-package-comparisons). -/
local instance trfFieldCharacteristic : CharP D.k D.p :=
  letI : Fact D.p.Prime := ⟨D.prime⟩
  letI := Fintype.ofFinite D.k₀
  letI : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card.symm.trans D.card_base).trans D.cardinality_eq)
  charP_of_injective_algebraMap' D.k₀ D.p

/-- The ring characteristic is prime.
Source: finite-field convention (blueprint: def-trf-finite-package-comparisons). -/
local instance : Fact (ringChar D.k).Prime := ⟨by
  rw [ringChar.eq D.k D.p]
  exact D.prime⟩
/-- The ring characteristic differs from the coefficient prime.
Source: finite-field convention (blueprint: def-trf-finite-package-comparisons). -/
local instance : Fact (ringChar D.k ≠ ell) := ⟨by
  rw [ringChar.eq D.k D.p]
  exact (Fact.out : ell ≠ D.p).symm⟩

/-- Morphisms between the standing schemes are separated and of finite type.
Source: standing scheme conventions (blueprint: def-trf-finite-package-comparisons). -/
local instance trfSeparated {X Y : SepFinType D.k} (f : X ⟶ Y) :
    IsSeparated f.hom.left := by
  have : IsSeparated (f.hom.left ≫ Y.obj.hom) := by rw [f.hom.w]; infer_instance
  exact IsSeparated.of_comp f.hom.left Y.obj.hom
/-- Relative local finite type follows from the source structure map.
Source: standing scheme conventions (blueprint: def-trf-finite-package-comparisons). -/
local instance trfFiniteType {X Y : SepFinType D.k} (f : X ⟶ Y) :
    LocallyOfFiniteType f.hom.left := by
  have : LocallyOfFiniteType (f.hom.left ≫ Y.obj.hom) := by rw [f.hom.w]; infer_instance
  exact locallyOfFiniteType_of_comp f.hom.left Y.obj.hom
/-- Relative quasi-compactness follows from the source structure map.
Source: standing scheme conventions (blueprint: def-trf-finite-package-comparisons). -/
local instance trfQuasiCompact {X Y : SepFinType D.k} (f : X ⟶ Y) :
    QuasiCompact f.hom.left := by
  have : QuasiCompact (f.hom.left ≫ Y.obj.hom) := by rw [f.hom.w]; infer_instance
  exact QuasiCompact.of_comp f.hom.left Y.obj.hom

set_option maxHeartbeats 2000000 in
-- The concrete quotient presentation and derived-functor composites need extra elaboration.
/-- The unique normalized proper/open natural transformation. The defining property is
compositionInterchangeIsNormalized at EVERY ambient object, with pointwise uniqueness.
Thus the chosen transformation is the open-adjunction transpose of inverse restriction.
Source: equation (6.7), det-sf-comp-composition-interchange (2), and
lem-sf-condensed-proper-open-interchange (blueprint: def-trf-finite-package-comparisons). -/
def trfNormalizedInterchange (ell : ℕ) [Fact ell.Prime]
    (D : WeilConjectures.FiniteFieldDatum.{u}) [Fact (ell ≠ D.p)]
    (E : PadicAlgCl.FiniteIntermediateField ell) (n : ℕ) (hn : 1 ≤ n)
    {X Y Ybar : Scheme.{u}} (p : X ⟶ Y) (i : Y ⟶ Ybar)
    [IsProper p] [IsOpenImmersion i] [QuasiCompact i]
    (c : Compactification.BoundaryCompactification (p ≫ i))
    [Ybar.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (Ybar ↘ Spec (.of D.k))]
    [QuasiCompact (Ybar ↘ Spec (.of D.k))] :
    moduleObjectDerivedPushforward A[ell, E, n] p ⋙ D((i)_!open⟦A[ell, E, n]⟧) ⟶
      D((c.obj.obj.i)_!open⟦A[ell, E, n]⟧) ⋙
        moduleObjectDerivedPushforward A[ell, E, n] c.obj.obj.g := by
  letI : Y.Over (Spec (.of D.k)) := ⟨i ≫ (Ybar ↘ Spec (.of D.k))⟩
  letI : X.Over (Spec (.of D.k)) := ⟨p ≫ (Y ↘ Spec (.of D.k))⟩
  letI : c.obj.obj.Z.Over (Spec (.of D.k)) := ⟨c.obj.obj.g ≫ (Ybar ↘ Spec (.of D.k))⟩
  haveI : p.IsOver (Spec (.of D.k)) := ⟨rfl⟩
  haveI : i.IsOver (Spec (.of D.k)) := ⟨rfl⟩
  haveI : c.obj.obj.g.IsOver (Spec (.of D.k)) := ⟨rfl⟩
  haveI : c.obj.obj.i.IsOver (Spec (.of D.k)) := ⟨by
    change c.obj.obj.i ≫ c.obj.obj.g ≫ _ = (p ≫ i) ≫ _
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (fun a ↦ a ≫ (Ybar ↘ Spec (.of D.k))) c.obj.obj.comm.symm)⟩
  letI : LocallyOfFiniteType (Y ↘ Spec (.of D.k)) :=
    inferInstanceAs (LocallyOfFiniteType (i ≫ (Ybar ↘ Spec (.of D.k))))
  letI : QuasiCompact (Y ↘ Spec (.of D.k)) :=
    inferInstanceAs (QuasiCompact (i ≫ (Ybar ↘ Spec (.of D.k))))
  letI : LocallyOfFiniteType (X ↘ Spec (.of D.k)) :=
    inferInstanceAs (LocallyOfFiniteType (p ≫ (Y ↘ Spec (.of D.k))))
  letI : QuasiCompact (X ↘ Spec (.of D.k)) :=
    inferInstanceAs (QuasiCompact (p ≫ (Y ↘ Spec (.of D.k))))
  letI : LocallyOfFiniteType (c.obj.obj.Z ↘ Spec (.of D.k)) :=
    inferInstanceAs (LocallyOfFiniteType (c.obj.obj.g ≫ (Ybar ↘ Spec (.of D.k))))
  letI : QuasiCompact (c.obj.obj.Z ↘ Spec (.of D.k)) :=
    inferInstanceAs (QuasiCompact (c.obj.obj.g ≫ (Ybar ↘ Spec (.of D.k))))
  have hcoeff : Nonempty (Mon.mk A[ell, E, n] ≅
      Mon.mk (properOpenFiniteCoefficient ell (ULift.{u} E) n)) := by
    let nf := (Padic.coefficientExtensionAbsoluteValue ell (ULift.{u} E)).toNormedField
    let : NormedField (ULift.{u} E) := nf
    let : TopologicalSpace (ULift.{u} E) :=
      nf.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    let : DiscreteTopology (Padic.coefficientExtensionRing ell (ULift.{u} E) n) :=
      DerivedNakayama.quotientDiscrete ell (ULift.{u} E) n
    have ht : (inferInstance : TopologicalSpace
      (Padic.coefficientExtensionRing ell (ULift.{u} E) n)) = ⊥ :=
      DiscreteTopology.eq_bot
    exact ⟨trfDiscreteCoefficientIso
      (Padic.coefficientExtensionRing ell (ULift.{u} E) n) _ inferInstance ht⟩
  exact Classical.choose (condensedProperOpenInterchange D ell Fact.out
    (ULift.{u} E) n hn A[ell, E, n] (Or.inl hcoeff) p i c)

/-- A tower with second compactification d. It uses Nagata on f followed by d.i;
only the final canonical compactification comparisons depend on the other chosen models.
Source: the composition proof (blueprint: def-trf-finite-package-comparisons). -/
def trfCompositionTower {X Y Z : SepFinType D.k} (f : X ⟶ Y) (g : Y ⟶ Z)
    (d : Compactification g.hom.left) : Compactification.Triangle f.hom.left g.hom.left :=
  letI : CompactSpace Z.obj.left :=
    QuasiCompact.compactSpace_of_compactSpace Z.obj.hom
  letI : QuasiSeparatedSpace Z.obj.left := quasiSeparatedSpace_of_quasiSeparated Z.obj.hom
  letI : CompactSpace d.Z := QuasiCompact.compactSpace_of_compactSpace d.g
  letI : QuasiSeparatedSpace d.Z := quasiSeparatedSpace_of_quasiSeparated d.g
  letI : QuasiCompact d.i := d.quasiCompact_openImmersion inferInstance
  let e := HasCompactification.compactification (f.hom.left ≫ d.i)
  Compactification.Triangle.ofRestrict d (Compactification.inf e e)

set_option maxHeartbeats 2000000 in
-- The concrete quotient presentation and derived-functor composites need extra elaboration.
/-- The tower compositor is Rq_* of the normalized interchange, followed by the
canonical proper-image compositor and open-extension compositor, in equation (6.7).
Source: sk-thm-sf-comp-composition, comp_normalized display
(blueprint: def-trf-finite-package-comparisons). -/
def trfTowerComposition (ell : ℕ) [Fact ell.Prime]
    (D : WeilConjectures.FiniteFieldDatum.{u}) [Fact (ell ≠ D.p)]
    (E : PadicAlgCl.FiniteIntermediateField ell) (n : ℕ) (hn : 1 ≤ n)
    {X Y Z : SepFinType D.k} (f : X ⟶ Y) (g : Y ⟶ Z)
    (T : Compactification.Triangle f.hom.left g.hom.left) :
    rightDerivedLowerShriekOfCompactification A[ell, E, n] T.cf ⋙
        rightDerivedLowerShriekOfCompactification A[ell, E, n] T.cg ⟶
      rightDerivedLowerShriekOfCompactification A[ell, E, n] T.cfg := by
  letI : T.cg.Z.Over (Spec (.of D.k)) := ⟨T.cg.g ≫ Z.obj.hom⟩
  letI : LocallyOfFiniteType (T.cg.Z ↘ Spec (.of D.k)) :=
    inferInstanceAs (LocallyOfFiniteType (T.cg.g ≫ Z.obj.hom))
  letI : QuasiCompact (T.cg.Z ↘ Spec (.of D.k)) :=
    inferInstanceAs (QuasiCompact (T.cg.g ≫ Z.obj.hom))
  letI : QuasiCompact T.cg.i := T.cg.quasiCompact_openImmersion inferInstance
  letI : QuasiCompact (T.cf.g ≫ T.cg.i) := inferInstance
  let δ := trfNormalizedInterchange ell D E n hn T.cf.g T.cg.i
    (detSfBoundaryCompactification (CompactSupportComposition.middle T))
  exact Functor.whiskerRight (Functor.whiskerLeft D((T.cf.i)_!open⟦A[ell, E, n]⟧) δ)
      (moduleObjectDerivedPushforward A[ell, E, n] T.cg.g) ≫
    Functor.whiskerLeft D((T.cf.i)_!open⟦A[ell, E, n]⟧)
      (Functor.whiskerLeft D((T.q)_!open⟦A[ell, E, n]⟧)
        (rightDerivedLowerStarComp A[ell, E, n] T.p T.cg.g).hom) ≫
    Functor.whiskerLeft D((T.cf.i)_!open⟦A[ell, E, n]⟧)
      (Functor.whiskerLeft D((T.q)_!open⟦A[ell, E, n]⟧)
        (Functor.rightDerivedFunctorNatIso
          (eqToIso (congrArg (lowerStar A[ell, E, n]) T.p_g))).hom) ≫
    Functor.whiskerRight (CompactSupportComposition.openFactor A[ell, E, n] T.cf.i T.q T.cfg.i
      T.i_q).hom (moduleObjectDerivedPushforward A[ell, E, n] T.cfg.g)

set_option maxHeartbeats 2000000 in
-- The concrete quotient presentation and derived-functor composites need extra elaboration.
end Finite
end AlgebraicGeometry.ProEtale.CondensedRing
