/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GeneralPurityTransport.GeneralTransportData
public import WeilConjectures.AlgebraicGeometry.ExplicitSmoothComparison.ExplicitSmoothAdjunctionData
public import WeilConjectures.AlgebraicGeometry.PurityCoefficientChange.CondensedPurityCoefficientChange
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportScalarLines
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedCoefficientMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
public import WeilConjectures.AlgebraicGeometry.RootCoordinateFace.RootTowerCoordinateFace
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenImmersionTensorProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersionTensorProjection
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.FieldTensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonPresentationSupplement
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonLocalizing
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
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
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralDerivedCoefficientData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralConstantModelLocalResolution
public import WeilConjectures.ProperBaseChange.IntegralLfpLocallyFreeResolution
public import WeilConjectures.ProperBaseChange.CondensedConstructibleSerre
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocallyClosedGeneratorTensorIntersection
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralLfpConstantModelComparison
public import WeilConjectures.AlgebraicGeometry.CondensedLocallyClosedExtensionTower
public import WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixAdmissibleThickness
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.AlgebraicGeometry.Locally.LocallyPerfectScalarModel
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicConstantLocalModelTor
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
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Shift
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
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
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
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
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestriction
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenClosedSequenceRingSheaf
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
public import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCycleClass
public import WeilConjectures.ZetaWeil.PodCtfAdjunctionData.PodCtfAdjunctions
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportScalar
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.CategoryTheory.SheafTensor
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import WeilConjectures.CategoryTheory.SmoothBaseChange.CohomologyInWeakSerreSubcategory
public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDescentTwoColimit
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.ModuleObjects.Linear
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
public import Mathlib.FieldTheory.Finite.Basic
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralModels
public import WeilConjectures.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousCoefficientModuleEncodingSupplement
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicIntegersInvertEll
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationMap
public import Mathlib.RingTheory.Localization.BaseChange
public import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralPushComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralModel
public import WeilConjectures.SixFunctors.Integral.IntegralModelsGenerators
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.PadicIntegersBoundedTriangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Bounded.BoundedConstructiblePushforwardRestriction
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import WeilConjectures.CategoryTheory.SmoothPurity.ComplexColimitHomotopyColimit
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedContinuitySections
public import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedContinuityDirectImage
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.Compactification.BoundaryRefinement
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
public import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
public import Mathlib.CategoryTheory.Linear.Yoneda
public import WeilConjectures.AlgebraicGeometry.IntegralConstructibleSheafHom
public import WeilConjectures.CategoryTheory.HomColimitExtension
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.NoetherianSpace
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteModelStratumFiltration
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Order.CompletePartialOrder
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartLisseExtensionConstructible
public import WeilConjectures.SixFunctors.TopologicalLisseIntegralClosure
public import WeilConjectures.SixFunctors.TopologicalIntegralConstructibility
public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalization
public import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
public import WeilConjectures.Compactification.Dense
public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekInterfaces
public import WeilConjectures.AlgebraicGeometry.SpCondensedIntegralAdjunction.IntegralAdjunctionBijectionStatement
public import WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import WeilConjectures.Algebra.Homology.System.SystemScalarCoherence
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImage
public import WeilConjectures.AlgebraicGeometry.ReductionExceptionalStatement
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityReductionTowerData
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportCompact
public import Mathlib.CategoryTheory.Shift.Adjunction
public import WeilConjectures.CategoryTheory.Right.RightExactTensorShiftCancellation
public import WeilConjectures.CategoryTheory.Derived.DerivedTensorRightExact
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleDerivedFunctorCompositorShifts
public import WeilConjectures.AlgebraicGeometry.IntegralModelsStatement
public import WeilConjectures.AlgebraicGeometry.CondensedIntegralTower.CondensedCoefficientTowers
public import WeilConjectures.AlgebraicGeometry.CondensedIntegralTower.CondensedNormalizedTowers
public import WeilConjectures.Algebra.Homology.Strict.StrictProjectionLimitData
public import WeilConjectures.ProperBaseChange.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.Integral.Constant.IntegralConstantModelRealizationSupplement
public import WeilConjectures.NumberTheory.Padics.LocalFieldIntegralBasis
public import WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
public import WeilConjectures.AlgebraicGeometry.ExactProductFunctorStrictLimit
public import WeilConjectures.CategoryTheory.Sites.FixedCoefficientDerivedChangeOfRings
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import WeilConjectures.AlgebraicGeometry.ReductionDirectImageFiniteCoefficients
public import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerGluingData
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerBound
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekData
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedTowers
import WeilConjectures.AlgebraicGeometry.SpChartAdmissibility.SmoothPurityTowerChartData
import WeilConjectures.AlgebraicGeometry.VaryingRingGraph.VaryingRingGraphSummand
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowersAbelian
import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekCalculus
import Mathlib.CategoryTheory.Localization.Predicate
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalization
import WeilConjectures.Compactification.CategoryBaseChange
import WeilConjectures.AlgebraicGeometry.SmoothPurity.CompactifiableCompatibleTower
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenCalculus
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonTorInterval
import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerTransitionCompatibility
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
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.CategoryTheory.RingedSliceExtensionExactness
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.SmoothPurity.ProEtaleWeaklyEtaleLocalization
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
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionCompatibilities
public import WeilConjectures.Algebra.Homology.RingedTensorSquare.RingedExchangeTensorCoherence
public import WeilConjectures.AlgebraicGeometry.SmoothPurityReductionTowerIntegralHeart
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdmissibleCondensedCoefficientFamily
import WeilConjectures.AlgebraicGeometry.ExplicitSmoothComparison.ComparisonBrownExplicit
import WeilConjectures.AlgebraicGeometry.ExplicitSmoothComparison.ComparisonBrownUnique
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
import WeilConjectures.Compactification.BoundaryRefinement
import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import WeilConjectures.CategoryTheory.CompactObject
import WeilConjectures.CategoryTheory.WeakTriangulatedGenerator
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
import WeilConjectures.CategoryTheory.Brown.BrownHypotheses
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocalizingCompactificationCoherence
import WeilConjectures.AlgebraicGeometry.SixFunctors.ShriekCoefficientIsomorphism
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import WeilConjectures.CategoryTheory.Brown.BrownHypothesesStructural
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteLocalizingExceptionalPreservation
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralCompactSupport.IntegralExceptionalRestriction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Rational.RationalRestrictionGlue
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.AdmissibleBoundedConstructibleTriangulated
import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc

/-! # Native condensed rational and algebraic-closure purity

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-setup/sec-the-purity-statement/sk-thm-purity-transport/
_section.md and sk-thm-purity-transport.proof.md, Steps 1--4
(blueprint: thm-pur-rational-and-qbar-purity).

The statement is phrased on the published interface of the smooth-purity transport
(`GeneralPurityTransport`, sk-thm-purity-transport): the six admissible coefficient
presentations `PurityTransport.Coefficient`, the native finite-Tor constructible
categories `Coefficient.ctf`, the actual compact-support functor `support`
(`Rf_! = R\bar f_* j_!`), the twisted pullback `source` (`Lf^*(-)(d)[2d]` with the
root-tower Tate line) and the restricted Brown adjoint `exceptional`.  The base field
is the algebraic closure `D.k` of the finite field of a `FiniteFieldDatum`, and the
prime `ℓ ≠ p` together with the chosen algebraic closure of `ℚ_ℓ` are those of a
`D.CoefficientDatum`.  The coefficient-change comparisons are those of
det-sp-purity-coefficient-change (`GeneralPurityCoefficientChange`) and of
det-sp-field-extension-towers (`NativeFieldTower`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.PurityTransport
open AlgebraicGeometry.ProEtale.GeneralPurityTransport
open AlgebraicGeometry.ProEtale.GeneralPurityCoefficientChange
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.NativeRationalQbarPurity

/-- The characteristic of the algebraic closure `D.k` is the datum's prime `p`.
Source: standing setting `k = \bar{\mathbf F}_q` (blueprint: thm-pur-rational-and-qbar-purity). -/
theorem ringChar_eq (D : WeilConjectures.FiniteFieldDatum.{u}) : ringChar D.k = D.p := by
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans (D.card_base.trans D.cardinality_eq))
  let : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  exact ringChar.eq D.k D.p

/-- The characteristic of `D.k` is prime.
Source: standing setting (blueprint: thm-pur-rational-and-qbar-purity). -/
theorem ringChar_prime (D : WeilConjectures.FiniteFieldDatum.{u}) :
    Fact (ringChar D.k).Prime :=
  ⟨(ringChar_eq D).symm ▸ D.prime⟩

/-- The coefficient prime differs from the characteristic of `D.k`.
Source: standing setting `ℓ ≠ char(k)` (blueprint: thm-pur-rational-and-qbar-purity). -/
theorem ringChar_ne (D : WeilConjectures.FiniteFieldDatum.{u}) (cD : D.CoefficientDatum) :
    Fact (ringChar D.k ≠ cD.l) :=
  ⟨by rw [ringChar_eq D]; exact cD.different.symm⟩

/-- `D.k = \bar{\mathbf F}_q` is algebraically closed, hence in the scope
"finite or algebraically closed" of the cited dependencies.
Source: standing setting (blueprint: thm-pur-rational-and-qbar-purity). -/
theorem baseScope (D : WeilConjectures.FiniteFieldDatum.{u}) : Finite D.k ∨ IsAlgClosed D.k :=
  Or.inr (IsAlgClosure.isAlgClosed D.k₀)

/-- A smooth datum of the transport framework as a geometric index of the explicit
smooth comparison: the same schemes, structure map of the target, smooth map, relative
dimension and compactification (only the separatedness over `k` is forgotten).
Source: det-sp-comparison-brown-explicit indices
(blueprint: thm-pur-rational-and-qbar-purity). -/
def toExplicitDatum {k : Type u} [Field k] (s : SmoothDatum k) :
    ExplicitSmoothComparison.Datum k where
  X := s.X.left
  Y := s.Y.left
  base := s.Y.hom
  map := s.map
  dim := s.dim
  compactification := s.compactification

/-- The restriction of an explicit smooth-comparison family
(det-sp-comparison-brown-explicit) to the smooth data of the transport framework:
at `s` it is literally the adjunction of the family at `toExplicitDatum s`.
Source: det-sp-comparison-brown-explicit, sk-thm-purity-transport
(blueprint: thm-pur-rational-and-qbar-purity). -/
def restrictFamily (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    (b : ExplicitSmoothComparison.Family ell k) : AdjunctionFamily ell k :=
  fun c s ↦
    { support_closed := (b c (toExplicitDatum s)).support_closed
      source_closed := (b c (toExplicitDatum s)).source_closed
      adjunction := (b c (toExplicitDatum s)).adjunction }

/-- The restricted family has the same counit (smooth trace) as the explicit family.
Source: det-sp-comparison-brown-explicit (blueprint: thm-pur-rational-and-qbar-purity). -/
theorem restrictFamily_trace (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    (b : ExplicitSmoothComparison.Family ell k) (c : Coefficient ell) (s : SmoothDatum k)
    (K : c.ctf ell s.Y.left) :
    (restrictFamily ell k b c s).trace K = (b c (toExplicitDatum s)).trace K :=
  rfl

private def continuousRingIso {A B : Type} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B]
    (e : A ≃+* B) (he : Continuous e) (hi : Continuous e.symm) :
    Mon.mk (Profinite.continuousMapRingObj.{u} A) ≅
      Mon.mk (Profinite.continuousMapRingObj.{u} B) := by
  let er : Profinite.continuousMapRingSheaf.{u} A ≅
      Profinite.continuousMapRingSheaf.{u} B :=
    { hom := Profinite.continuousMapRingSheafMap e.toRingHom he
      inv := Profinite.continuousMapRingSheafMap e.symm.toRingHom hi
      hom_inv_id := by
        ext S x
        apply ULift.ext
        apply ContinuousMap.ext
        intro t
        exact e.symm_apply_apply _
      inv_hom_id := by
        ext S x
        apply ULift.ext
        apply ContinuousMap.ext
        intro t
        exact e.apply_symm_apply _ }
  let ea := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso er
  have : IsMonHom ea.hom := Sheaf.isMonHom_sheafCompose_map _ er.hom
  have : IsMonHom ea.inv := Sheaf.isMonHom_sheafCompose_map _ er.inv
  exact
    { hom := Mon.ofHom ea.hom
      inv := Mon.ofHom ea.inv
      hom_inv_id := Mon.Hom.ext ea.hom_inv_id
      inv_hom_id := Mon.Hom.ext ea.inv_hom_id }

set_option maxHeartbeats 4000000 in
-- Elaborating the native derived category restrictions exceeds the default heartbeat limit.
private theorem baseCoefficientPresentations (ell : ℕ) [Fact ell.Prime] :
    (∃ E : PadicAlgCl.FiniteIntermediateField ell,
      Nonempty (Mon.mk (Profinite.continuousMapRingObj.{u} ℤ_[ell]) ≅
        Mon.mk (Profinite.padicIntegersRingObj.{u} ell E))) ∧
    (∃ E : PadicAlgCl.FiniteIntermediateField ell,
      Nonempty (Mon.mk (Profinite.continuousMapRingObj.{u} ℚ_[ell]) ≅
        Mon.mk (Profinite.continuousMapRingObj.{u} E))) := by
  let E : PadicAlgCl.FiniteIntermediateField ell := ⟨⊥, inferInstance⟩
  let := PadicAlgCl.normedFieldOfAlgebra ell E
  let e := (IntermediateField.botEquiv ℚ_[ell] (PadicAlgCl ell)).symm.toRingEquiv
  have hn (x : ℚ_[ell]) : ‖e x‖ = ‖x‖ := by
    change ‖algebraMap E (PadicAlgCl ell) (e x)‖ = ‖x‖
    change ‖algebraMap ℚ_[ell] (PadicAlgCl ell) x‖ = ‖x‖
    exact PadicAlgCl.norm_extends ell x
  have he : Isometry e := AddMonoidHomClass.isometry_of_norm e hn
  have hi : Isometry e.symm := by
    intro x y
    simpa only [e.apply_symm_apply] using (he (e.symm x) (e.symm y)).symm
  let ez : ℤ_[ell] ≃+* PadicAlgCl.integers ell E :=
    { toFun := fun x ↦ ⟨e x.val, by
        change ‖e x.val‖₊ ≤ 1
        exact_mod_cast (hn x.val ▸ x.property)⟩
      invFun := fun y ↦ ⟨e.symm y.val, by
        have h := hn (e.symm y.val)
        rw [e.apply_symm_apply] at h
        change ‖e.symm y.val‖ ≤ 1
        rw [← h]
        exact_mod_cast y.property⟩
      left_inv := fun x ↦ Subtype.ext (e.symm_apply_apply _)
      right_inv := fun y ↦ Subtype.ext (e.apply_symm_apply _)
      map_add' := fun x y ↦ Subtype.ext (map_add e _ _)
      map_mul' := fun x y ↦ Subtype.ext (map_mul e _ _) }
  have hz : Isometry ez := AddMonoidHomClass.isometry_of_norm ez (fun x ↦ hn x.val)
  have hzi : Isometry ez.symm := by
    intro x y
    simpa only [ez.apply_symm_apply] using (hz (ez.symm x) (ez.symm y)).symm
  exact ⟨⟨E, ⟨continuousRingIso ez hz.continuous hzi.continuous⟩⟩,
    ⟨E, ⟨continuousRingIso e he.continuous hi.continuous⟩⟩⟩

set_option maxHeartbeats 4000000 in
-- Elaborating the native derived category restrictions exceeds the default heartbeat limit.
private theorem coefficientPresentations (D : WeilConjectures.FiniteFieldDatum.{u})
    (cD : D.CoefficientDatum) :
    (∀ c : Coefficient cD.l, IsAdmissibleCoefficientFor cD (Mon.mk (c.obj.{u} cD.l))) ∧
    ∀ (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X],
      IsAdmissibleCoefficientFor cD Λ →
        ∃ c : Coefficient cD.l, Nonempty (Λ ≅ Mon.mk (c.obj.{u} cD.l)) := by
  constructor
  · intro c
    cases c with
    | finite A fin n hA =>
      let : TopologicalSpace A := ⊥
      let : DiscreteTopology A := discreteTopology_bot A
      exact Or.inl ⟨A, inferInstance, fin, inferInstance, inferInstance, inferInstance,
        ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n), hA⟩, ⟨Iso.refl _⟩⟩
    | integers =>
      obtain ⟨E, hE⟩ := (baseCoefficientPresentations.{u} cD.l).1
      exact Or.inr (Or.inl ⟨E, hE⟩)
    | rationals =>
      obtain ⟨E, hE⟩ := (baseCoefficientPresentations.{u} cD.l).2
      exact Or.inr (Or.inr (Or.inl ⟨E, hE⟩))
    | integral E => exact Or.inr (Or.inl ⟨E, ⟨Iso.refl _⟩⟩)
    | rational E => exact Or.inr (Or.inr (Or.inl ⟨E, ⟨Iso.refl _⟩⟩))
    | closure => exact Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩))
  · intro Λ _ h
    rcases h with ⟨A, hA, hfin, htop, hd, hr, ⟨r, hpos, hann⟩, he⟩ |
      ⟨E, he⟩ | ⟨E, he⟩ | he
    · have ht : htop = ⊥ := @DiscreteTopology.eq_bot A htop hd
      subst htop
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
      exact ⟨.finite (.of A) hfin n hann, he⟩
    · exact ⟨.integral E, he⟩
    · exact ⟨.rational E, he⟩
    · exact ⟨.closure, he⟩

-- The transpose of the unit word is the identity: precompose by the invertible
-- compact-support comparison, use its naturality, then the counit square and triangle.
set_option maxHeartbeats 4000000 in
-- Elaborating the native derived category restrictions exceeds the default heartbeat limit.
private theorem unit_of_counit
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {F : C ⥤ D} {J : D ⥤ C} {F' : C' ⥤ D'} {J' : D' ⥤ C'}
    (adj : F ⊣ J) (adj' : F' ⊣ J') (T : C ⥤ C') (S : D ⥤ D')
    (b : F ⋙ S ⟶ T ⋙ F')
    (α : ∀ K, T.obj (J.obj K) ⟶ J'.obj (S.obj K))
    (hc : ∀ K, b.app (J.obj K) ≫ F'.map (α K) ≫ adj'.counit.app (S.obj K) =
      S.map (adj.counit.app K)) (M : C) [Epi (b.app M)] :
    T.map (adj.unit.app M) ≫ α (F.obj M) ≫ J'.map (b.app M) =
      adj'.unit.app (T.obj M) := by
  apply (adj'.homEquiv _ _).symm.injective
  dsimp only [Functor.id_obj, Functor.comp_obj]
  rw [Adjunction.homEquiv_symm_unit]
  rw [Adjunction.homEquiv_counit]
  apply (cancel_epi (b.app M)).1
  calc
    b.app M ≫ (F'.map (T.map (adj.unit.app M) ≫ α (F.obj M) ≫ J'.map (b.app M)) ≫
        adj'.counit.app (F'.obj (T.obj M))) =
      (b.app M ≫ F'.map (T.map (adj.unit.app M))) ≫ F'.map (α (F.obj M)) ≫
        adj'.counit.app (S.obj (F.obj M)) ≫ b.app M := by
          simp only [Functor.map_comp, Category.assoc]
          have hn := adj'.counit.naturality (b.app M)
          dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map] at hn
          rw [hn]
    _ = S.map (F.map (adj.unit.app M)) ≫
        (b.app (J.obj (F.obj M)) ≫ F'.map (α (F.obj M)) ≫
          adj'.counit.app (S.obj (F.obj M))) ≫ b.app M := by
            have hn := b.naturality (adj.unit.app M)
            dsimp only [Functor.comp_map, Functor.id_obj, Functor.comp_obj] at hn
            rw [← hn]
            simp only [Category.assoc]
    _ = S.map (F.map (adj.unit.app M)) ≫ S.map (adj.counit.app (F.obj M)) ≫
        b.app M := by rw [hc]
    _ = b.app M ≫ 𝟙 _ := by
      have ht : F.map (adj.unit.app M) ≫ adj.counit.app (F.obj M) = 𝟙 _ :=
        adj.left_triangle_components M
      rw [← S.map_comp_assoc, ht, S.map_id]
      simp only [Category.id_comp, Category.comp_id]

set_option maxHeartbeats 4000000 in
-- Elaborating the native derived category restrictions exceeds the default heartbeat limit.
set_option maxHeartbeats 4000000 in
-- Elaborating the native derived category restrictions exceeds the default heartbeat limit.
set_option maxHeartbeats 4000000 in
-- Elaborating the native derived category restrictions exceeds the default heartbeat limit.
set_option maxHeartbeats 4000000 in
-- Assembling the native adjunctions requires unfolding their large category restrictions.
end AlgebraicGeometry.ProEtale.NativeRationalQbarPurity
