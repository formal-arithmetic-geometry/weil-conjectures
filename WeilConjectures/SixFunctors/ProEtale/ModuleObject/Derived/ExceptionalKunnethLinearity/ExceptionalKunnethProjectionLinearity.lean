/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.FiniteTraceFormulaConventions.FiniteTraceFormulaConventions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProductComparisons.NativeSixFunctorKunnethMaps2
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedCoefficientUnitConstructible
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

/-!
# Projection linearity of the identity-factor exceptional Künneth map

Source: latest blueprint, part-duality-trace-formula/sec-lefschetz-verdier/
sec-trace-classes-and-the-lefschetz-verdier-formula/sk-d-trace-class/
lem-trf-trace-class-diagonal-pairing.proof.md, Step 3(c).
(blueprint: lem-trf-exceptional-kunneth-projection-linearity).

The exceptional comparison is the existing counit-defined `alphaUnit`. The action below
is the adjunction transpose of the signed inverse projection followed by the counit.
The membership and invertibility witnesses are conclusions, not additional hypotheses.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing.ExceptionalKunnethLinearity

open CompactificationReindexing RelativeKunneth ProductComparisons

/-- The coefficient ring is exactly the discrete finite ring of the recorded conventions.
Source: the finite coefficient convention in Step 3(c)
(blueprint: lem-trf-exceptional-kunneth-projection-linearity). -/
abbrev coefficient (T : WeilConjectures.FiniteTraceFormulaConventions.{u}) :
    ScalarSixRing.{u} := ⟨T.coefficients⟩

/-- The existing finite-primary admissibility condition, in the convention's small coordinates.
Source: arbitrary finite primary coefficients, Wei Yang #1423
(blueprint: lem-trf-exceptional-kunneth-projection-linearity). -/
instance coefficientAdmissibility (T : WeilConjectures.FiniteTraceFormulaConventions.{u}) :
    Fact (IsLocalizingAdmissibleCoefficient T.ell (coefficient T).X) where
  out := by
    let : TopologicalSpace (Shrink.{0} T.A) := ⊥
    let : DiscreteTopology (Shrink.{0} T.A) := ⟨rfl⟩
    let : IsTopologicalRing (Shrink.{0} T.A) := DiscreteTopology.topologicalRing
    refine Or.inl ⟨Shrink.{0} T.A, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, ?_, ⟨Iso.refl _⟩⟩
    obtain ⟨N, _, hN⟩ := T.primary
    have hn : ((T.ell ^ N : ℕ) : Shrink.{0} T.A) = 0 := by
      apply (Shrink.ringEquiv.{0} T.A).injective
      simpa only [map_natCast, map_zero, nsmul_eq_mul, mul_one] using hN
    exact ⟨N, fun a ↦ by simp only [nsmul_eq_mul, hn, zero_mul]⟩

/-- The already recorded relative theorem, with its explicitly normalized comparison word.
Source: def-sf-kv-maps (i) and relative Künneth (iv)
Its type is `ProductTheorem T.ell T.datum.k (finiteFieldParameters T.datum T.ell _)`, with
the characteristic proof built below
(blueprint: lem-trf-exceptional-kunneth-projection-linearity). -/
def relativeDatum (T : WeilConjectures.FiniteTraceFormulaConventions.{u}) :=
  ProductComparisons.relativeDatum T.datum T.ell (by
    let : Fintype T.datum.k₀ := Fintype.ofFinite T.datum.k₀
    let : Fact T.datum.p.Prime := ⟨T.datum.prime⟩
    let : CharP T.datum.k₀ T.datum.p := charP_of_card_eq_prime_pow
      ((Nat.card_eq_fintype_card (α := T.datum.k₀)).symm.trans
        (T.datum.card_base.trans T.datum.cardinality_eq))
    let : CharP T.datum.k T.datum.p :=
      charP_of_injective_algebraMap' T.datum.k₀ T.datum.p
    simpa only [ringChar.eq T.datum.k T.datum.p] using T.ell_ne.symm)

/-- The actual coefficient unit in degree zero, bundled by its existing constructibility theorem.
Source: omega_Y = Ra_Y^! A_s in Step 3(c)
(blueprint: lem-trf-exceptional-kunneth-projection-linearity). -/
def coefficientUnit (T : WeilConjectures.FiniteTraceFormulaConventions.{u}) :
    ConstantModelConstructibleFiniteTor (coefficient T).X (Spec (.of T.datum.k)) :=
  ⟨constantCoefficientObject (coefficient T).X _, constantCoefficientObject_mem _ _⟩

/-- Its specified derived tensor-unit identification, without choosing an endpoint isomorphism.
Source: the unit normalization of def-sf-kv-maps (iv)
(blueprint: lem-trf-exceptional-kunneth-projection-linearity). -/
def coefficientUnitIso (T : WeilConjectures.FiniteTraceFormulaConventions.{u}) :
    (coefficientUnit T).obj ≅ 𝟙_ (D (coefficient T).X (Spec (.of T.datum.k))) := by
  unfold coefficientUnit constantCoefficientObject
  exact DerivedCategory.singleFunctorObjUnitIso
    (Mod (Sheaf (ProEt.topology (Spec (.of T.datum.k))) Ab.{u + 1})
      (condensedRingObj (coefficient T).X (Spec (.of T.datum.k))))

section Action

variable (Λ : ScalarSixRing.{u}) {X Z : Scheme.{u}} {p : Z ⟶ X}
  (c : Compactification p) (S : SixOperationsLocalizingAdjunction Λ.X c)
  (L M : ConstantModelConstructibleFiniteTor Λ.X X)

/-- Reassociation followed by the inverse canonical derived pullback tensor comparison.
Source: rho in the statement, using the canonical comparison of
lem-weil-pbc-ringed-topoi-derived-tensor-pullback
(blueprint: lem-trf-exceptional-kunneth-projection-linearity). -/
def rho (Q : D Λ.X Z) :
    (P Λ.X p).obj L.obj ⊗ ((P Λ.X p).obj M.obj ⊗ Q) ≅
      (P Λ.X p).obj (L.obj ⊗ M.obj) ⊗ Q :=
  (α_ _ _ _).symm ≪≫ tensorIso (pullTensor Λ p L.obj M.obj).symm (Iso.refl Q)

/-- Exactly the counit mate m_p(L,M). The only supplied witnesses concern membership
and invertibility of the specified projection arrow. Its inverse is conjugated by
both signed symmetries, placing L on the left. No inverse of alpha is used.
Source: the definition of m_p in Step 3(c)
(blueprint: lem-trf-exceptional-kunneth-projection-linearity). -/
def action
    (hLM : (constantModelBoundedConstructible Λ.X X ⊓
      _root_.DerivedCategory.finiteTorAmplitude _) (L.obj ⊗ M.obj))
    (hDomain : (constantModelBoundedConstructible Λ.X Z ⊓
      _root_.DerivedCategory.finiteTorAmplitude _)
        ((P Λ.X p).obj L.obj ⊗ ((exceptional Λ S).obj M).obj))
    (hPF : IsIso (pf Λ.X c ((exceptional Λ S).obj M).obj L.obj)) :
    (P Λ.X p).obj L.obj ⊗ ((exceptional Λ S).obj M).obj ⟶
      ((exceptional Λ S).obj ⟨L.obj ⊗ M.obj, hLM⟩).obj :=
  let := hPF
  ((adjunction Λ S).homEquiv
    ⟨(P Λ.X p).obj L.obj ⊗ ((exceptional Λ S).obj M).obj, hDomain⟩
    ⟨L.obj ⊗ M.obj, hLM⟩
    ⟨(F Λ.X c).map (symmetry Λ _ _ _).hom ≫
      inv (pf Λ.X c ((exceptional Λ S).obj M).obj L.obj) ≫
      (symmetry Λ _ _ _).hom ≫
      (𝟙 L.obj ⊗ₘ ((adjunction Λ S).counit.app M).hom)⟩).hom

end Action

end AlgebraicGeometry.ProEtale.CondensedRing.ExceptionalKunnethLinearity
