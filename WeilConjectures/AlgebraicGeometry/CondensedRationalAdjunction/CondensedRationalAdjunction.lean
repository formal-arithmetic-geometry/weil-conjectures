/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportScalarLines
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralModels
public import WeilConjectures.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousCoefficientModuleEncodingSupplement
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicIntegersInvertEll
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationMap
public import Mathlib.RingTheory.Localization.BaseChange
public import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralPushComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralModel
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
public import WeilConjectures.SixFunctors.Integral.IntegralModelsGenerators
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.PadicIntegersBoundedTriangulated
public import WeilConjectures.AlgebraicGeometry.SpIntegralAdjunction.IntegralReconstructionComparisonData
public import WeilConjectures.AlgebraicGeometry.IntegralReconstructionComparisons.IntegralReconstructionComparisons
public import WeilConjectures.AlgebraicGeometry.Picard.SpTwistedPullback.TwistedPullbackReductionData
public import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
public import WeilConjectures.AlgebraicGeometry.SpTowerGamma.SmoothPurityTowerGammaData
public import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerGluingData
import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekInterfaces
import WeilConjectures.AlgebraicGeometry.SpChartAdmissibility.SmoothPurityTowerChartData
import WeilConjectures.AlgebraicGeometry.VaryingRingGraph.VaryingRingGraphSummand
import Mathlib.CategoryTheory.Localization.Predicate
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalization
import WeilConjectures.Compactification.CategoryBaseChange
import WeilConjectures.AlgebraicGeometry.SmoothPurity.CompactifiableCompatibleTower
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenCalculus
import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.Algebra.Homology.Ringed.RingedOpenTotalTensorKFlat
import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenMatePasting
import WeilConjectures.AlgebraicGeometry.VaryingRing.SemilinearScalarRestriction
import WeilConjectures.AlgebraicGeometry.SmoothPurity.ChartNormalizedModelIdentification
import WeilConjectures.AlgebraicGeometry.ProperOpenCalculus.CompactificationRefinementCoherence
import WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.EtaleProEtaleCoefficientCompatibility
import WeilConjectures.AlgebraicGeometry.AdjunctionTransfer.EtaleCtfChartDomain
import WeilConjectures.CategoryTheory.ExactDerivedPasting.Word.ExactDerivedTransformationPasting
import WeilConjectures.AlgebraicGeometry.Finite.Compact.FiniteCompactSupportDomains
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.TowerGeometryAdjunctionEvaluation
import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingProperOpenPasting
import WeilConjectures.CategoryTheory.RingedSliceExtensionExactness
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.SmoothPurity.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.Compactification.Dense
import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityEtaleNormalization
import WeilConjectures.AlgebraicGeometry.SpCoordinateAdjunction.SmoothPurityCoordinateRightComparisons
import WeilConjectures.AlgebraicGeometry.SpChartAdmissibility.SmoothPurityTowerChartAdmissibility
import WeilConjectures.AlgebraicGeometry.SpTowerP1.SmoothPurityTowerP1Adjunction
import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceTower
import WeilConjectures.AlgebraicGeometry.SpCoordinateAdjunction.SmoothPurityCoordinateCategories
import WeilConjectures.AlgebraicGeometry.SmoothOfRelativeDimension.SmoothAdmissibleCoordinateCover
import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerBinaryPairGluing
import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerPairOpenRestriction2
import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerLocalCounitRepresentability
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalRealization
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalChart
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalConservativity
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImage
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.SmoothPurityMap
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothPurityMaps
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.SpTowerP1.TowerP1CoefficientCoordinates
public import WeilConjectures.AlgebraicGeometry.SpTowerP1.TowerP1GeometricCoordinates
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothTensorDuality
public import WeilConjectures.AlgebraicGeometry.Finite.General.FiniteGeneralRing
public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekCalculus
public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerTransitionCompatibility
public import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekLevels
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowers
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedTowers
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.PurityDiagonalDualizingObject
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.SpChartAdmissibility.SmoothPurityTowerBoundsOperations
public import WeilConjectures.Algebra.Homology.ProperBaseChange.KFlatResolutionGeneral
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.AlgebraicGeometry.SmoothPurity.TowerOperationsGroundFieldRetagging
import WeilConjectures.AlgebraicGeometry.SpFiniteOrientation.FiniteOrientationReduction
import WeilConjectures.SmoothPurity.Finite.FiniteLineTensorConditions
import WeilConjectures.AlgebraicGeometry.Finite.FiniteLocallyFreeLineModels
import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorRealization
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryMonoidal
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonTorInterval
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.SpTowerProjection.TowerCompactSupportProjectionFormula
public import Mathlib.FieldTheory.Finite.Basic
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalSmoothnessFiniteComparison
public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekData
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedEquivalence
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerBound
public import WeilConjectures.SmoothPurity.IntegralLineReduction.IntegralLineReductionRestriction
public import WeilConjectures.SmoothPurity.Integral.IntegralPullbackSystemComparison
public import WeilConjectures.SmoothPurity.Pur.PurReductionLimitShiftAdjunction
public import WeilConjectures.Algebra.Homology.Signed.SignedLineScalarTensorTower
public import WeilConjectures.AlgebraicGeometry.Picard.IntegralStrictReductionModel
public import WeilConjectures.SmoothPurity.Adic.AdicPuritySourceReduction
public import WeilConjectures.SmoothPurity.Supporting.SignedTwistFirstReduction
public import WeilConjectures.SmoothPurity.Supporting.SignedLineTensorEquivalence
public import WeilConjectures.Algebra.Homology.LineUnbounded.LineUnboundedDerivedTensor
public import WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.Picard.SpTwistedPullback.TwistedPullbackLineMembership
public import Mathlib.Algebra.CharP.CharAndCard
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
public import WeilConjectures.AlgebraicGeometry.CompleteCompactificationLimit.CompleteCompactificationLimitSupport
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import WeilConjectures.AlgebraicGeometry.CompleteCompactificationLimit.CompleteCompactificationLimitRealization
public import WeilConjectures.AlgebraicGeometry.FieldShriekSystem.FieldShriekSystemComparison
public import WeilConjectures.SmoothPurity.Integral.Twist.IntegralTwistDerivedScalarCanonical
public import WeilConjectures.SixFunctors.Supporting.ConstantCoefficientScalarNormalization
public import WeilConjectures.FourierTransform.CompletedScalarShift
public import WeilConjectures.FourierTransform.CompletedLineTensor.CompletedLineTensorCoherence
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionUniverses
public import WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.SmoothPurity.Supporting.TwistPreservesFiniteness
public import WeilConjectures.SmoothPurity.Integral.IntegralCtfTriangulated
public import WeilConjectures.SmoothPurity.Completed.CompletedScalarChainShift
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.SmoothPurity.Integral.Twist.IntegralTwistBaseChange
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleLinear
public import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportRealization
public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisons
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRTower
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.ZetaWeil.ConstantGeometricStalkUnit.ConstantGeometricStalkUnit
public import WeilConjectures.FourierTransform.IntegralCompletedComparison.IntegralPullbackShiftCoordinates
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
public import WeilConjectures.DeligneLaumon.SfScalarExtensionComposition
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityReductionTowerNormalized
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import WeilConjectures.SmoothPurity.Supporting.DirectImagesConstructible
public import WeilConjectures.AlgebraicGeometry.FieldExceptionalSystem.FieldExceptionalSystemLaws
public import WeilConjectures.AlgebraicGeometry.FieldExceptionalSystem.FieldExceptionalSystemIso
public import WeilConjectures.CategoryTheory.ProperBaseChange.ExchangeMateCube
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionCompatibilities
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.Data.Nat.Prime.Infinite
public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingMap
public import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.IntegralDirectImageTower
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousModuleEncodingUniverses
public import WeilConjectures.CategoryTheory.ScalarLocalization.SemilinearScalarLocalization
public import WeilConjectures.ProperBaseChange.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import WeilConjectures.CategoryTheory.K.KInjectiveTotalDerivedLinear
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Algebra.Homology.OrdinaryLineScalar.OrdinaryLineDerivedScalarComparison
public import WeilConjectures.Algebra.Homology.DerivedTensorConstraints.DerivedTensorAdditiveConstraints
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.Compactification.RefinementCategory
public import Mathlib.CategoryTheory.Adjunction.Unique
public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralCompactificationSystemRealization
public import WeilConjectures.Algebra.Homology.System.SystemRingedSequenceSite
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingTensorComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.Algebra.Homology.SequenceProjection.SequenceProjectionDerivedAdjunction
public import WeilConjectures.Algebra.Homology.SequenceProjection.SequencePushforwardLimitProjections
public import WeilConjectures.Algebra.Homology.RingedTensorSquare.RingedExchangeTensorCoherence
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalization
public import WeilConjectures.CategoryTheory.RingedDerivedComparisons.RingedDerivedMonoidalComparisons
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.AlgebraicGeometry.Picard.SiteDerivedTensorDescentIndependentCoefficients
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Homology.KFlatFixedTensor.KFlatFixedTensorTriangulatedSupplement
public import Mathlib.CategoryTheory.Products.Associator
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorComparisonOfUniverses
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.Algebra.Homology.SmoothPurity.TotalTensorSignedCoherence
public import WeilConjectures.SecSmoothPurity.CochainPullbackTensorShift
public import WeilConjectures.AlgebraicGeometry.Picard.KFlatRingedToposPullback
public import WeilConjectures.SecSmoothPurity.CochainComparisonMonoidalEquationsSupplement
public import WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitPullbackData
public import WeilConjectures.SmoothPurity.Adic.AdicPurityObjects
public import WeilConjectures.SmoothPurity.Adic.AdicPurityExceptionalReduction
public import WeilConjectures.SmoothPurity.IntegralSystemRealization.IntegralOperationShiftData
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.SixFunctors.ConstructibleExceptionalCompositorData2
public import WeilConjectures.SmoothPurity.PurUnitTrace.AdicUnitTraceReductionData
public import WeilConjectures.SmoothPurity.PurUnitTrace.AdicUnitTraceScalarData
public import WeilConjectures.SmoothPurity.Pur.PurAdicReconstruction
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonClassAdjunction
public import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SmoothPurity.RationalSmoothPurityCanonical.RationalSmoothPurityCanonical
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcRationalCategory
public import WeilConjectures.CategoryTheory.StageSystem.PbcQbarCategory
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowersAbelian
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.Finite.General.FiniteGeneralRingData
public import WeilConjectures.AlgebraicGeometry.TowerAdjointCompositor.TowerAdjointCompositorRealization
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.ShriekTensorCompositionSupplement
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality
public import WeilConjectures.AlgebraicGeometry.SfEtaleCompactProjectionCoherence
public import WeilConjectures.AlgebraicGeometry.SfExceptionalTensorTransitivity
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.SmoothTrace
public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.ProEtaleOrderedIntegration
public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.FiniteSiteTensorProjection
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedSiteAdjunctionTranspose
public import WeilConjectures.AlgebraicGeometry.Vector.VectorBundleIntegrationCharts
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.AffineDiagonalTateCoordinates
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalSmoothnessComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModuleIntrinsicComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjComparison
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorUpperBound
public import WeilConjectures.AlgebraicGeometry.ProEtale.Replete
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftComplete
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.AlgebraicGeometry.Finite.Type.FiniteTypeFibreDimensionBound
public import WeilConjectures.AlgebraicGeometry.Proper.ProperTorsionDirectImageBound
public import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
public import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.Mathlib.CategoryTheory.NatIso
import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalSmoothnessTheorem
import WeilConjectures.AlgebraicGeometry.SpTowerMate.SmoothPurityTowerMateEvaluationReduction
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantExact
import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitudeProEtaleModule
import WeilConjectures.AlgebraicGeometry.Sf.SfFiniteExceptionalInverseImage
import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.SmoothBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Vector.VectorPurityNormalization
import WeilConjectures.AlgebraicGeometry.SpTowerMate.SmoothPurityTowerMateEvaluationReduction
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantExact
import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitudeProEtaleModule
import WeilConjectures.AlgebraicGeometry.Sf.SfFiniteExceptionalInverseImage
import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.SmoothBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Vector.VectorPurityNormalization
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSectionIntegratedSpecialization
import WeilConjectures.SmoothPurity.Supporting.DiagonalExchangeCube
import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalSmoothnessTheorem
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.EquivalenceAdjunctionComparisonSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import WeilConjectures.AlgebraicGeometry.SpIntegralAdjunction.IntegralReconstructionComparisonData
import WeilConjectures.AlgebraicGeometry.IntegralReconstructionComparisons.IntegralReconstructionComparisons
import WeilConjectures.AlgebraicGeometry.Picard.SpTwistedPullback.TwistedPullbackReductionData
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import WeilConjectures.AlgebraicGeometry.SpTowerGamma.SmoothPurityTowerGammaData
import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerGluingData

import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalRealization
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalChart
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalConservativity
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImage
import WeilConjectures.SmoothPurity.PurityFiniteSetting.SmoothPurityMap
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothPurityMaps
import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
import WeilConjectures.AlgebraicGeometry.SpTowerP1.TowerP1CoefficientCoordinates
import WeilConjectures.AlgebraicGeometry.SpTowerP1.TowerP1GeometricCoordinates
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothTensorDuality
import WeilConjectures.AlgebraicGeometry.Finite.General.FiniteGeneralRing
import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekCalculus
import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerTransitionCompatibility
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekLevels
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowers
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedTowers
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.PurityDiagonalDualizingObject
import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.SpChartAdmissibility.SmoothPurityTowerBoundsOperations
import WeilConjectures.Algebra.Homology.ProperBaseChange.KFlatResolutionGeneral
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility

import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonTorInterval
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.SpTowerProjection.TowerCompactSupportProjectionFormula
import Mathlib.FieldTheory.Finite.Basic
import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalSmoothnessFiniteComparison
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekData
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedEquivalence
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerBound
import WeilConjectures.SmoothPurity.IntegralLineReduction.IntegralLineReductionRestriction
import WeilConjectures.SmoothPurity.Integral.IntegralPullbackSystemComparison
import WeilConjectures.SmoothPurity.Pur.PurReductionLimitShiftAdjunction
import WeilConjectures.Algebra.Homology.Signed.SignedLineScalarTensorTower
import WeilConjectures.AlgebraicGeometry.Picard.IntegralStrictReductionModel
import WeilConjectures.SmoothPurity.Adic.AdicPuritySourceReduction
import WeilConjectures.SmoothPurity.Supporting.SignedTwistFirstReduction
import WeilConjectures.SmoothPurity.Supporting.SignedLineTensorEquivalence
import WeilConjectures.Algebra.Homology.LineUnbounded.LineUnboundedDerivedTensor
import WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
import WeilConjectures.AlgebraicGeometry.Picard.SpTwistedPullback.TwistedPullbackLineMembership
import Mathlib.Algebra.CharP.CharAndCard
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
import WeilConjectures.AlgebraicGeometry.CompleteCompactificationLimit.CompleteCompactificationLimitSupport
import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import Mathlib.CategoryTheory.Adjunction.Restrict
import WeilConjectures.AlgebraicGeometry.CompleteCompactificationLimit.CompleteCompactificationLimitRealization
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleLinear
import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
import WeilConjectures.DeligneLaumon.SfScalarExtensionComposition
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingMap
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousCoefficientModuleEncodingSupplement
import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.IntegralDirectImageTower
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousModuleEncodingUniverses
import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
import WeilConjectures.AlgebraicGeometry.Integral.IntegralModels
import WeilConjectures.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicIntegersInvertEll
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationMap
import Mathlib.RingTheory.Localization.BaseChange
import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralPushComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralModel
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
import WeilConjectures.SixFunctors.Integral.IntegralModelsGenerators
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.PadicIntegersBoundedTriangulated
import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportRealization
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionUniverses
import WeilConjectures.CategoryTheory.ScalarLocalization.SemilinearScalarLocalization
import WeilConjectures.ProperBaseChange.RingedStrictTowerHomotopyLimitIndependentCoefficients
import WeilConjectures.CategoryTheory.K.KInjectiveTotalDerivedLinear
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Algebra.Homology.OrdinaryLineScalar.OrdinaryLineDerivedScalarComparison
import WeilConjectures.Algebra.Homology.DerivedTensorConstraints.DerivedTensorAdditiveConstraints
import Mathlib.Logic.Small.Defs
import Mathlib.CategoryTheory.Limits.HasLimits

/-! # The native condensed rational purity adjunction

Source: latest blueprint, sec-smooth-purity/sk-prop-sp-rational,
sk-prop-sp-rational-adjunction.md, (1)--(2)
(blueprint: prop-pur-condensed-rational-adjunction).

The integral adjunction is an input, supplied by the integral counit realization.
Every rational functor below acts on the native condensed finite-Tor category.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.PurityTransport
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRationalAdjunction

/-- Bundle the actual inclusion of continuous integral coefficients into E.
Source: rational-adjunction (1), scalar extension
(blueprint: prop-pur-condensed-rational-adjunction). -/
def coefficientMap (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell) :
    (Coefficient.integral E).bundled.{u} ell ⟶ (Coefficient.rational E).bundled ell :=
  CommMon.homMk (Mon.Hom.mk (padicIntegersRingObjToContinuousMapRingObj ell E))

/-- Restrict the prescribed total derived scalar extension using only a membership proof.
Source: rational-adjunction (1), Q_T
(blueprint: prop-pur-condensed-rational-adjunction). -/
def extend (ell : ℕ) [Fact ell.Prime] (E : PadicAlgCl.FiniteIntermediateField ell)
    (T : Scheme.{u})
    (h : ∀ K, property ell (.integral E) T K → property ell (.rational E) T
      ((scalarSixChange (coefficientMap ell E) T).obj K)) :
    (Coefficient.integral E).ctf ell T ⥤ (Coefficient.rational E).ctf ell T :=
  (property ell (.rational E) T).lift
    ((property ell (.integral E) T).ι ⋙ scalarSixChange (coefficientMap ell E) T)
    (fun K ↦ h K.obj K.property)

/-- The two endpoint comparisons with the prescribed ambient normalizations.
Their fields contain actual isomorphisms; the normalization fields fix their maps.
Source: rational-adjunction (1), the comparisons a and b
(blueprint: prop-pur-condensed-rational-adjunction). -/
structure Comparisons (ell : ℕ) [Fact ell.Prime]
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (E : PadicAlgCl.FiniteIntermediateField ell) (s : SmoothDatum D)
    (A₀ : ExplicitAdjunction ell D (.integral E) s)
    (A : ExplicitAdjunction ell D (.rational E) s)
    (hX : ∀ K, property ell (.integral E) s.X.left K → property ell (.rational E) s.X.left
      ((scalarSixChange (coefficientMap ell E) s.X.left).obj K))
    (hY : ∀ K, property ell (.integral E) s.Y.left K → property ell (.rational E) s.Y.left
      ((scalarSixChange (coefficientMap ell E) s.Y.left).obj K)) where
  coefficient_normalization :
    (Coefficient.integral E).integralMap ell ≫ (coefficientMap ell E).hom.hom =
      (Coefficient.rational E).integralMap ell
  line : ScalarLineCoordinates ell (coefficientMap ell E) coefficient_normalization s.X.left
  b : support ell (.integral E) s.compactification A₀.support_closed ⋙ extend ell E s.Y.left hY ≅
    extend ell E s.X.left hX ⋙ support ell (.rational E) s.compactification A.support_closed
  a : source ell (.integral E) s.map s.dim A₀.source_closed ⋙ extend ell E s.X.left hX ≅
    extend ell E s.Y.left hY ⋙ source ell (.rational E) s.map s.dim A.source_closed
  b_normalized : ∀ M : (Coefficient.integral E).ctf ell s.X.left,
    (b.hom.app M).hom = (scalarSupportMap (coefficientMap ell E) s.compactification).app M.obj
  a_normalized : ∀ K : (Coefficient.integral E).ctf ell s.Y.left,
    (a.hom.app K).hom =
      sourceScalar ell (coefficientMap ell E) s.map s.dim coefficient_normalization line K.obj

/-- All clauses of the rational adjunction, on the actual condensed categories.
The pure-tensor equation holds for every pair of models and every identification.
Together with additivity and E-linearity, it uniquely specifies the displayed tensor
Hom composite and its independence of choices. Source: rational-adjunction (1)--(2)
(blueprint: prop-pur-condensed-rational-adjunction). -/
structure Laws (ell : ℕ) [Fact ell.Prime]
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (E : PadicAlgCl.FiniteIntermediateField ell) (s : SmoothDatum D)
    (A₀ : ExplicitAdjunction ell D (.integral E) s)
    (A : ExplicitAdjunction ell D (.rational E) s)
    (hX : ∀ K, property ell (.integral E) s.X.left K → property ell (.rational E) s.X.left
      ((scalarSixChange (coefficientMap ell E) s.X.left).obj K))
    (hY : ∀ K, property ell (.integral E) s.Y.left K → property ell (.rational E) s.Y.left
      ((scalarSixChange (coefficientMap ell E) s.Y.left).obj K))
    (c : Comparisons ell D E s A₀ A hX hY) : Prop where
  modelsX : ∀ M : (Coefficient.rational E).ctf ell s.X.left,
    ∃ M₀ : (Coefficient.integral E).ctf ell s.X.left,
      Nonempty ((extend ell E s.X.left hX).obj M₀ ≅ M)
  modelsY : ∀ K : (Coefficient.rational E).ctf ell s.Y.left,
    ∃ K₀ : (Coefficient.integral E).ctf ell s.Y.left,
      Nonempty ((extend ell E s.Y.left hY).obj K₀ ≅ K)
  hom_add : ∀ (M : (Coefficient.rational E).ctf ell s.X.left)
    (K : (Coefficient.rational E).ctf ell s.Y.left)
    (z z' : (support ell (.rational E) s.compactification A.support_closed).obj M ⟶ K),
    A.adjunction.homEquiv M K (z + z') =
      A.adjunction.homEquiv M K z + A.adjunction.homEquiv M K z'
  hom_smul : ∀ (M : (Coefficient.rational E).ctf ell s.X.left)
    (K : (Coefficient.rational E).ctf ell s.Y.left)
    (z : (support ell (.rational E) s.compactification A.support_closed).obj M ⟶ K)
    (e : E.1),
    A.adjunction.homEquiv M K (scale ell E s.Y.left e z) =
      scale ell E s.X.left e (A.adjunction.homEquiv M K z)
  model_formula : ∀ (M₀ : (Coefficient.integral E).ctf ell s.X.left)
    (K₀ : (Coefficient.integral E).ctf ell s.Y.left)
    (M : (Coefficient.rational E).ctf ell s.X.left)
    (K : (Coefficient.rational E).ctf ell s.Y.left)
    (i : (extend ell E s.X.left hX).obj M₀ ≅ M)
    (j : (extend ell E s.Y.left hY).obj K₀ ≅ K)
    (h : (support ell (.integral E) s.compactification A₀.support_closed).obj M₀ ⟶ K₀)
    (e : E.1),
    A.adjunction.homEquiv M K
      ((support ell (.rational E) s.compactification A.support_closed).map i.inv ≫
        c.b.inv.app M₀ ≫ scale ell E s.Y.left e ((extend ell E s.Y.left hY).map h) ≫ j.hom) =
      i.inv ≫ scale ell E s.X.left e
        ((extend ell E s.X.left hX).map (A₀.adjunction.homEquiv M₀ K₀ h)) ≫
        c.a.hom.app K₀ ≫ (source ell (.rational E) s.map s.dim A.source_closed).map j.hom
  unit : ∀ M₀ : (Coefficient.integral E).ctf ell s.X.left,
    A.adjunction.unit.app ((extend ell E s.X.left hX).obj M₀) =
      (extend ell E s.X.left hX).map (A₀.adjunction.unit.app M₀) ≫
        c.a.hom.app _ ≫ (source ell (.rational E) s.map s.dim A.source_closed).map
          (c.b.hom.app M₀)
  counit : ∀ K₀ : (Coefficient.integral E).ctf ell s.Y.left,
    c.b.hom.app _ ≫ (support ell (.rational E) s.compactification A.support_closed).map
        (c.a.hom.app K₀) ≫ A.adjunction.counit.app ((extend ell E s.Y.left hY).obj K₀) =
      (extend ell E s.Y.left hY).map (A₀.adjunction.counit.app K₀)
  brown : ∀ (G : (Coefficient.rational E).ctf ell s.Y.left ⥤
      (Coefficient.rational E).ctf ell s.X.left)
    (adj : support ell (.rational E) s.compactification A.support_closed ⊣ G),
    ∃! gamma : source ell (.rational E) s.map s.dim A.source_closed ≅ G,
      ∀ K, (support ell (.rational E) s.compactification A.support_closed).map
        (gamma.hom.app K) ≫ adj.counit.app K = A.adjunction.counit.app K

end AlgebraicGeometry.ProEtale.CondensedRationalAdjunction
