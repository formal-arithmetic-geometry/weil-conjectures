/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.CondensedCoefficientPoint
public import WeilConjectures.ZetaWeil.PodCtfAdjunctionData.PodCtfAdjunctions
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
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.WeaklyEtaleIhom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.RightDual
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableProjectiveUnit
public import WeilConjectures.CategoryTheory.ModuleObjects.FinitelyPresentedMap
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
public import Mathlib.Data.Finset.Max
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.AdmissibleBoundedConstructibleTriangulated
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedLisseProEtaleLocality
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedPointModuleComparison
public import WeilConjectures.Algebra.Homology.Monoidal.Dual
public import WeilConjectures.TraceFormula.CategoricalTraceBiproduct
public import WeilConjectures.CategoryTheory.ModuleObjects.FreeMap
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.Algebra.Field.ULift
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators
public import WeilConjectures.AlgebraicGeometry.Pullback.PullbackFiniteConstantLocalModel
public import WeilConjectures.ConstructibleSheaf.OpenClosed
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Dualizable
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureExistence
public import WeilConjectures.AlgebraicGeometry.SixFunctors.BrownHypothesesSmall
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.EllAdic.EllAdicLocalizingExceptionalBounded
public import WeilConjectures.CategoryTheory.SixFunctors.CohomologicalSolutionSetRepresentability
public import WeilConjectures.CategoryTheory.SixFunctors.SetGeneratedDerivedSolutionSet
public import WeilConjectures.CategoryTheory.SmoothPurity.CountableCoproductsIdempotentComplete
public import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
public import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
public import Mathlib.CategoryTheory.Triangulated.Yoneda
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedOpenClosedInternalHomMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedOpenClosedInternalHom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportDerivedLocalization
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
public import WeilConjectures.CategoryTheory.Brown.BrownHypothesesCriteria
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
public import WeilConjectures.Compactification.Over
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Mathlib.CategoryTheory.Adjunction.Unique
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenImmersionTensorProjection
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportProjectionFormula
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.FieldTensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonPresentationSupplement
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonLocalizing
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.SixFunctors.NativeInternalHomExact
public import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory
public import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded.IntegralModelsEmbedded
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
public import WeilConjectures.CategoryTheory.ObjectProperty.Duality
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedVerdierCoefficientComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCtfInternalEtaleRealization
public import WeilConjectures.AlgebraicGeometry.FiniteNativeTensor.FiniteNativeTensorComparison
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalCompactSupportSiteComparison
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingPullbackFixed
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.CategoryTheory.SixFunctors.OrdinaryModuleDerivedInternalHom
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteKInjectiveResolutionsMixedUniverses
public import WeilConjectures.CategoryTheory.SmoothPurity.QuasiIsoHomComplexMapMixedUniverses
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEquivalence
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import WeilConjectures.SixFunctors.Etale.Derived.VerdierBiduality
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek
public import WeilConjectures.SixFunctors.Etale.Derived.WeilComplexDual
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteCoefficientSmallCarrierComparison
public import Mathlib.CategoryTheory.Yoneda
public import WeilConjectures.CategoryTheory.Constant.ConstantScalarRestrictionTensorSupplement
public import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FiniteFieldDualizingPullback
public import WeilConjectures.SixFunctors.Etale.Derived.DoubleDual
public import WeilConjectures.CategoryTheory.RingObjects.EllAdic
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsFlat
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import WeilConjectures.AlgebraicGeometry.Internal.InternalFirstResidueRingIsoSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
public import WeilConjectures.AlgebraicGeometry.Base.BaseFieldCohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.Embedded.EmbeddedIntegralCompletenessTransport
public import WeilConjectures.SixFunctors.ProEtale.InternalCompletionStacksComparison
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralModels
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientFiniteDescentObjects
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientFiniteDescentHom
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.ProEtaleCoefficients.DerivedNakayamaResolution
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedNakayamaFirstReduction
public import WeilConjectures.AlgebraicGeometry.PrincipalTensorScalarExtension
public import Mathlib.Algebra.Homology.Double
public import WeilConjectures.AlgebraicGeometry.Locally.LocallyPerfectScalarModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedScalarCoefficientMaps
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Shift
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixCtfGenerators
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleOrigin
public import WeilConjectures.AlgebraicGeometry.Flat.FlatModelGeneration
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleLisseModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleExtensionIso
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartLocallyClosedExtension
public import Mathlib.CategoryTheory.Triangulated.Generators
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
public import Mathlib.Topology.Defs.Filter
public import Mathlib.CategoryTheory.Monoidal.Mod
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
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedCoefficientMaps
public import WeilConjectures.AlgebraicGeometry.RootCoordinateFace.RootTowerCoordinateFace
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
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
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProEtaleProperOpenInterchange
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import WeilConjectures.AlgebraicGeometry.LocallyClosedExtensionData.LocallyClosedExtensionCoherence
public import WeilConjectures.CategoryTheory.AdjunctionSquareComposition
public import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarGeometricExchangeRectangle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenExtensionConstructibleFiniteTor
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientRefinement
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingLowerShriekCompositionModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestrictionMaps
public import WeilConjectures.Compactification.BaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
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
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafClosedLocalization
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafBaseChangeMates
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
public import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCycleClass
public import Mathlib.CategoryTheory.MorphismProperty.Retract
public import WeilConjectures.CategoryTheory.SixFunctors.ContravariantIsoLocus
public import Mathlib.CategoryTheory.Shift.Adjunction
public import WeilConjectures.CategoryTheory.Right.RightExactTensorShiftCancellation
public import WeilConjectures.CategoryTheory.Derived.DerivedTensorRightExact
public import WeilConjectures.AlgebraicGeometry.Native.NativeDerivedHomNormalizedShift
public import WeilConjectures.AlgebraicGeometry.Tensor.TensorHomShiftComparisonComponent
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleTensorShiftCancellationNaturality
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ImmersionProjectionScalarNormalization
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Triangulated.Functor
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
public import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import WeilConjectures.CategoryTheory.RingedDerivedComparisons.RingedDerivedMonoidalComparisons
public import WeilConjectures.CategoryTheory.Scalar.ScalarInternalHomDataSupplement
public import WeilConjectures.SmoothPurity.Coefficient.CoefficientSystemScalarCalculus
public import WeilConjectures.CategoryTheory.SixFunctors.SignedDerivedInternalHomExact
public import WeilConjectures.CategoryTheory.SixFunctors.EvaluationShiftTransport
public import WeilConjectures.CategoryTheory.RingedSignedTensor.RingedTensorSignedCancellation
public import WeilConjectures.SixFunctors.Coefficient.Tensor.CoefficientTensorCurryNormalization
public import WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
public import WeilConjectures.CategoryTheory.Scalar.ScalarHomComparisonTower
public import WeilConjectures.Algebra.Homology.Derived.DerivedScalarExtensionCounitShift
public import WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Retract
public import WeilConjectures.CategoryTheory.Monoidal.Closed.IhomComparison
public import WeilConjectures.CategoryTheory.Monoidal.Dualizable
public import WeilConjectures.ConstructibleSheaf.OpenClosedStratification
public import WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsUnit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ContinuousMapComparison
public import WeilConjectures.NumberTheory.Padics.IntegersShrinkModPow
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteDualityMaps
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.CategoryTheory.SignedDoubleHomCone.SignedDoubleHomConeSupplement
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import WeilConjectures.DeligneLaumon.FieldShriekCompositionQcqs
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.SixFunctors.CommonStageCompactWeilCohomology
public import WeilConjectures.SmoothPurity.Finite.FiniteCoefficientPoint
public import WeilConjectures.AlgebraicGeometry.Compactification.PureDimension
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import WeilConjectures.PoincareDuality.ProjectionFormula
import WeilConjectures.AlgebraicGeometry.Base.BaseFieldCohomologicalDimension
import WeilConjectures.SmoothPurity.CondensedOrdinaryCompactSections
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficients
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteDualityMaps
import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
import WeilConjectures.CategoryTheory.SignedDoubleHomCone.SignedDoubleHomConeSupplement
import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import WeilConjectures.DeligneLaumon.FieldShriekCompositionQcqs
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.SixFunctors.CommonStageCompactWeilCohomology
import WeilConjectures.SmoothPurity.Finite.FiniteCoefficientPoint
import WeilConjectures.AlgebraicGeometry.Compactification.PureDimension
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import WeilConjectures.CategoryTheory.Projection.ProjectionInternalHom
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Evaluation-normalized closed comparison at the condensed geometric point

Source: current blueprint, sec-six-functors/sk-thm-sf-package/
thm-pod-identification-of-the-comparison.proof.md, third paragraph
(blueprint: lem-pod-condensed-point-closed-comparison).

All derived categories, tensor products and internal Homs are the actual unbounded
derived constructions, restricted to the recorded constructible finite-Tor objects.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v w z
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedPointClosedComparison

section Closed
variable {C : Type u} {D : Type v} [Category.{w} C] [Category.{z} D]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalClosed C] [MonoidalClosed D]
  (F : C ⥤ D) [F.Monoidal]

/-- The closed comparison is the transpose of mapped evaluation after the
inverse of tau. Thus it is a fixed map, rather than a supplied isomorphism.
It is the component of the recorded `Functor.LaxMonoidal.ihomComparison`, the mate
of the tensorator, i.e. `curry (μ F U [U, V] ≫ F.map ev)`; that is the comparison
used by lem-sf-condensed-geometric-point-perfect, so no second notion is introduced.
Source: blueprint comparison proof, third paragraph
(blueprint: lem-pod-condensed-point-closed-comparison). -/
def comparison (U V : C) : F.obj ((ihom U).obj V) ⟶ (ihom (F.obj U)).obj (F.obj V) :=
  (Functor.LaxMonoidal.ihomComparison F U).natTrans.app V

/-- The coefficient-dual map includes the specified unit comparison u0.
Source: blueprint comparison proof, third paragraph
(blueprint: lem-pod-condensed-point-closed-comparison). -/
def coefficientDual (U : C) :
    F.obj ((ihom U).obj (𝟙_ C)) ⟶ (ihom (F.obj U)).obj (𝟙_ D) :=
  curry (Functor.LaxMonoidal.μ F U ((ihom U).obj (𝟙_ C)) ≫
    F.map ((ihom.ev U).app (𝟙_ C)) ≫ (Functor.Monoidal.εIso F).inv)

/-- An identity exceptional adjoint is represented by its actual adjunction.
The counit comparison is the unique right-adjoint comparison with the identity.
Source: blueprint comparison proof, identity-point normalization
(blueprint: lem-pod-condensed-point-closed-comparison). -/
def identityCounit (S : C ⥤ C) (adj : 𝟭 C ⊣ S) : S.obj (𝟙_ C) ≅ 𝟙_ C :=
  (adj.rightAdjointUniq Adjunction.id).app (𝟙_ C)

/-- The point Verdier comparison uses evaluation into omega and the identity
exceptional counit, in precisely that order.
Source: blueprint comparison proof, third paragraph and inverse identification
(blueprint: lem-pod-condensed-point-closed-comparison). -/
def pointVerdier (S : C ⥤ C) (adj : 𝟭 C ⊣ S) (U : C) :
    F.obj ((ihom U).obj (S.obj (𝟙_ C))) ⟶ (ihom (F.obj U)).obj (𝟙_ D) :=
  curry (Functor.LaxMonoidal.μ F U ((ihom U).obj (S.obj (𝟙_ C))) ≫
    F.map ((ihom.ev U).app (S.obj (𝟙_ C)) ≫ (identityCounit S adj).hom) ≫
    (Functor.Monoidal.εIso F).inv)

end Closed

open AlgebraicGeometry.ProEtale.CondensedGeometricPoint
open AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k]

/-- Restrict the fixed extension J(P) = Lambda_s tensor over B with P to perfect
complexes. Only membership is supplied; objects and arrows are the existing construction.
Source: blueprint comparison proof, first point-equivalence assertion
(blueprint: lem-pod-condensed-point-closed-comparison). -/
def perfectRealization (h : ∀ P : (perfect Λ).FullSubcategory,
    ctf Λ k ((condensedScalarRealization Λ (Spec (.of k))).obj P.obj)) :=
  (ctf Λ k).lift ((perfect Λ).ι ⋙ condensedScalarRealization Λ (Spec (.of k))) h

/-- The inherited braidings are specified on the exact ambient localization
used by each full subcategory. This spells out the standard Koszul descent
without identifying the scalar category's localization and Grothendieck universes.
Source: blueprint comparison proof, canonical monoidal point equivalence
(blueprint: lem-pod-condensed-point-closed-comparison). -/
def BraidedStatement (D₀ : WeilConjectures.FiniteFieldDatum.{u})
    [hc : ObjectProperty.IsMonoidal (ctf Λ D₀.k)]
    [hp : ObjectProperty.IsMonoidal (perfect Λ)]
    [ObjectProperty.IsMonoidalClosed (ctf Λ D₀.k)]
    [ObjectProperty.IsMonoidalClosed (perfect Λ)]
    (hF : ∀ K : (ctf Λ D₀.k).FullSubcategory, perfect Λ ((fiber Λ D₀.k).obj K.obj)) : Prop :=
  letI : HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} (condensedScalarRing Λ)) :=
    HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} _
  letI : BraidedCategory (ctf Λ D₀.k).FullSubcategory :=
    @ObjectProperty.fullBraidedSubcategory _ _ _ (ctf Λ D₀.k) hc
      (_root_.DerivedCategory.braidedCategory' _)
  letI : BraidedCategory (perfect Λ).FullSubcategory :=
    @ObjectProperty.fullBraidedSubcategory _ _ _ (perfect Λ) hp
      (_root_.DerivedCategory.braidedCategory'.{u + 1}
        (ModuleCat.{u + 1} (condensedScalarRing Λ)))
  ∃ m : (restricted Λ D₀.k hF).Braided,
    MonoidalStatement Λ D₀ hF m.toMonoidal

/-- Full direct point comparison, including the canonical inverse functor, tensor
and unit coherence, closed transposes and the global diagram.
Source: blueprint comparison proof, third paragraph
(blueprint: lem-pod-condensed-point-closed-comparison). -/
def Statement (D₀ : WeilConjectures.FiniteFieldDatum.{u}) : Prop :=
  ∃ (hc : ObjectProperty.IsMonoidal (ctf Λ D₀.k))
    (hp : ObjectProperty.IsMonoidal (perfect Λ))
    (hch : ObjectProperty.IsMonoidalClosed (ctf Λ D₀.k))
    (hph : ObjectProperty.IsMonoidalClosed (perfect Λ))
    (hF : ∀ K : (ctf Λ D₀.k).FullSubcategory, perfect Λ ((fiber Λ D₀.k).obj K.obj))
    (hJ : ∀ P : (perfect Λ).FullSubcategory,
      ctf Λ D₀.k ((condensedScalarRealization Λ (Spec (.of D₀.k))).obj P.obj))
    (adj : perfectRealization Λ D₀.k hJ ⊣ restricted Λ D₀.k hF),
    IsIso adj.unit ∧ IsIso adj.counit ∧
    @BraidedStatement Λ _ _ D₀ hc hp hch hph hF

end AlgebraicGeometry.ProEtale.CondensedPointClosedComparison
