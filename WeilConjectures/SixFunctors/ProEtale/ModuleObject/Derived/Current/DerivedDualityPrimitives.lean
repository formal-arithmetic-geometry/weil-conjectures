/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Current.SfIdentificationStatementData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Current.CurrentGlobalVerdierDuality
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixCtf
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedCoefficientMaps
import WeilConjectures.AlgebraicGeometry.RootCoordinateFace.RootTowerCoordinateFace
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntTensorProjection
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdmissibleTensorConstructibility
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
import WeilConjectures.Compactification.Over
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
import Mathlib.CategoryTheory.Triangulated.Adjunction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixFiniteGeneration
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixNonfiniteGeneration
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixAdmissibleThickness
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixPerfectExtension
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixCtfGenerators
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientProjectionSquare
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientsFiniteFree
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralDerivedIso
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.QlbarDirectImageComparison
import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.FiniteFreeScalarDerivedComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteScalarProjectionCase
import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarRestrictionMateNormalization
import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarMateProjection
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralFinitePointResolution
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorComparison
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedScalarCoefficientMaps
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProEtaleProperOpenInterchange
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.SixFunctors.ScalarOpenCompositorCoherence
import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarGeometricExchangeRectangle
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenExtensionConstructibleFiniteTor
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientRefinement
import WeilConjectures.CategoryTheory.AdjunctionSquareComposition
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteCoefficientSmallCarrierComparison
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingLowerShriekCompositionModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestrictionMaps
import WeilConjectures.Compactification.BaseChange
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonLocalizing
import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import WeilConjectures.CategoryTheory.CompactGeneratorsBuildObjects
import WeilConjectures.CategoryTheory.CompactObject
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingEtaleCompactGenerators
import Mathlib.Algebra.CharP.CharAndCard
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Formal.FormalClosedSupportDerived
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalTowerCoefficients
import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerLimit
import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerTrace
import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1Triangle
import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1UnitCounit
import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestriction
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenClosedSequenceRingSheaf
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
import WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement
import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCycleClass
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorHom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedCtfSixFunctorStabilityCurrent
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixHomTensorShiftCancellation
import Mathlib.Algebra.Homology.DerivedCategory.Linear
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Current.SfIdentificationStatementData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Current.SfIdentificationStatementData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Current.IdentificationPointCupShift
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Current.IdentificationProjectionCupShift
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.IsoId
import WeilConjectures.AlgebraicGeometry.PurityTransport.SmoothDualizingAllCoefficients
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.CategoryTheory.Monoidal.Closed.InvertibleDualizing
import Mathlib.CategoryTheory.Shift.Adjunction
import Mathlib.Algebra.Group.Int.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.NativeTateLineInvertible2
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.NativeSitePerfectDual
import WeilConjectures.SixFunctors.SfIdentificationData
import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
import WeilConjectures.AlgebraicGeometry.SixFunctors.PointProEtaleSectionsExactOfUniverses
import WeilConjectures.CategoryTheory.SixFunctors.OrdinaryModuleDerivedInternalHom
import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteKInjectiveResolutionsMixedUniverses
import WeilConjectures.CategoryTheory.SmoothPurity.QuasiIsoHomComplexMapMixedUniverses
import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import WeilConjectures.SmoothPurity.CondensedOrdinaryCompactSections
import WeilConjectures.ProEtaleCoefficients.DerivedNakayamaResolution
import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
import WeilConjectures.PoincareDuality.Abstract
import Mathlib.Topology.KrullDimension
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Field.ULift
import WeilConjectures.ProEtaleCoefficients.DerivedNakayamaResolution
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import WeilConjectures.ProEtaleCoefficients.DerivedNakayamaResolution
import WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
import Mathlib.Algebra.Ring.Shrink
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FinitePointScalarRealization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FinitePointScalarRings
import Mathlib.Algebra.Field.ULift
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
import WeilConjectures.Compactification.BoundaryPreparation
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocalizingCompactificationCoherence
import Mathlib.Algebra.CharP.CharAndCard
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.AlgebraicGeometry.SmoothPurity.DimensionExtension
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import Mathlib.Topology.KrullDimension
import Mathlib.Algebra.Field.ULift
import WeilConjectures.ProEtaleCoefficients.DerivedNakayamaResolution
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import WeilConjectures.AlgebraicGeometry.Integral.IntegralLfpConstantModelComparison
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import Mathlib.Algebra.Ring.Shrink
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteConstructibleEncoding
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteRestrictionEncodingSupplement
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedDirectImageBoundedBelow
import WeilConjectures.SixFunctors.Etale.Derived.DirectImageAmplitude
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
import WeilConjectures.AlgebraicGeometry.Open.OpenExtensionConstantModelConstructible
import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import WeilConjectures.AlgebraicGeometry.ProEtale.SepClosedPointLift
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
import WeilConjectures.WeilObject.Sheaf.Stalk
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.SepClosedPoint
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ConstructibleNakayama
import WeilConjectures.AlgebraicGeometry.Integral.IntegralPositiveReductionConstructible
import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleFiniteHeart
import WeilConjectures.AlgebraicGeometry.Integral.Residue.IntegralResidueCriterion
import WeilConjectures.AlgebraicGeometry.Integral.IntegralDirectImageLimits
import WeilConjectures.AlgebraicGeometry.Integral.IntegralDirectImageReductionCone
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
import WeilConjectures.Compactification.Over
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionLocalizing
import WeilConjectures.CategoryTheory.DerivedCategory.CoproductsOfHomologyProperty
import Mathlib.Algebra.Field.ULift
import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import WeilConjectures.ProEtaleCoefficients.DerivedNakayamaResolution
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralPushComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructibleExtensionByZero
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.QlbarDirectImageComparison
import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Complete
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Types.Filtered
import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.ConstructibleSheaf.FreeLifting
import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralStratum
import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralGluing
import WeilConjectures.AlgebraicGeometry.CondensedFinitePresentationDescent
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FinitePointIntegralCoefficientIso
import WeilConjectures.AlgebraicGeometry.Integral.IntegralContinuousEncodingConstructible
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.CategoryTheory.DerivedCategory.Bounded.BoundedHeartAmplitude
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Algebra.Module.Projective
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleStratum
import WeilConjectures.PoincareDuality.VerdierBiduality
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FinitePointSectionsExact
import WeilConjectures.SixFunctors.Integral.ScalarCompositionPairing
import WeilConjectures.SixFunctors.Coefficient.CoefficientDuality
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.RingTheory.Noetherian.Defs
import WeilConjectures.RingTheory.NoetherianPseudoCoherentCohomologyCriterion
import WeilConjectures.CategoryTheory.DerivedCategory.Perfect.PerfectCohomologyAssembly
import WeilConjectures.RingTheory.DiscreteValuationRing.QuotientDuality
import WeilConjectures.CategoryTheory.DerivedCategory.Perfect.Dualizable
import WeilConjectures.CategoryTheory.ObjectProperty.Duality
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.SimpleModule.InjectiveProjective
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedScalarRealization
import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded.IntegralModelsEmbedded
import Mathlib.Algebra.Module.Shrink
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.AlgebraicGeometry.Native.NativeHomSourceShiftData
import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
import WeilConjectures.Algebra.Homology.TensorHomologyPairing
import WeilConjectures.Algebra.Homology.ProjectiveHomEvaluationModel
import WeilConjectures.PoincareDuality.GlobalTwistInterchange.GlobalTwistInterchange

/-! # Degreewise Poincare duality over coefficient fields

Source: latest blueprint, `sk-thm-derived-duality`, both displayed pairings and
its proper clause (blueprint: sk-thm-derived-duality).
The inverse point Tate line is represented by the scalar dual of the positive
point Tate line, with its canonical evaluation. Its pairing is characterized by
inserting every section of the positive line in the actual derived pairing.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj CategoryTheory.Functor TensorProduct
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [local instance 10000] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [local instance 20000] HasDerivedCategory.ofIsGrothendieckAbelian

namespace AlgebraicGeometry.ProEtale.CondensedRing.Current

/-- Scalar and inverse-line perfectness for one specified derived pairing.
`Q` and `U` include the shift [2d]; hence H^(-i) is H^(2d-i) of the
unshifted complex. `T` is scalar realization of the positive point Tate line.
The surjective section-value map prevents an empty normalization condition.
The last two bijectivities are the two adjoints of the line-valued pairing.
Source: proof Steps 2--3 (blueprint: sk-thm-derived-duality). -/
def FieldDegreewiseAssertion {F : Type u} [Field F]
    {P Q U T : DerivedCategory (ModuleCat.{u} F)} {A : Type v}
    (b : P ⊗ Q ⟶ 𝟙_ _)
    (value : A → (DerivedCategory.homologyFunctor (ModuleCat.{u} F) 0).obj T)
    (insert : A → (U ⟶ Q)) : Prop :=
  Nonempty (Module.Basis (Fin 1) F ((DerivedCategory.homologyFunctor (ModuleCat.{u} F) 0).obj T)) ∧
  Function.Surjective value ∧
  ∀ i : ℤ,
    Module.Finite F ((DerivedCategory.homologyFunctor (ModuleCat.{u} F) i).obj P) ∧
    Module.Finite F ((DerivedCategory.homologyFunctor (ModuleCat.{u} F) (-i)).obj Q) ∧
    Module.Finite F ((DerivedCategory.homologyFunctor (ModuleCat.{u} F) (-i)).obj U) ∧
    (degreePairing b i).IsPerfPair ∧
    ∃ B : ((DerivedCategory.homologyFunctor (ModuleCat.{u} F) i).obj P) →ₗ[F]
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} F) (-i)).obj U) →ₗ[F]
          Module.Dual F ((DerivedCategory.homologyFunctor (ModuleCat.{u} F) 0).obj T),
      (∀ (a : A) (x : (DerivedCategory.homologyFunctor (ModuleCat.{u} F) i).obj P)
          (y : (DerivedCategory.homologyFunctor (ModuleCat.{u} F) (-i)).obj U),
        B x y (value a) = degreePairing b i x
          (((DerivedCategory.homologyFunctor (ModuleCat.{u} F) (-i)).map (insert a)).hom y)) ∧
      Function.Bijective B ∧ Function.Bijective B.flip

set_option maxHeartbeats 1600000 in
-- Native scalar-extension and module-pullback comparisons require nested derived reductions.
/-- Pull back the native positive Tate line, using its root-normalized
coordinates and the published scalar/pullback comparison along `e`.
Source: the canonical twist comparison in proof Step 3
(blueprint: sk-thm-derived-duality). -/
def degreeTwistPull (ell : ℕ) [Fact ell.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (c : PurityTransport.Coefficient ell)
    (e : c.bundled.{u} ell ≅ (⟨Λ⟩ : ScalarSixRing.{u}))
    {X s : Scheme.{u}} (a : X ⟶ s)
    (p : PurityTransport.LinePullCoordinates ell c a) (d : ℕ) :
    (scalarSixPull (⟨Λ⟩ : ScalarSixRing.{u}) a).obj
      (currentTwist ell Λ c e s d) ≅ currentTwist ell Λ c e X d :=
  ((PurityTransport.scalarPullbackIso e.hom a).symm.app
      ((DerivedCategory.singleFunctor _ 0).obj (c.line ell s d))) ≪≫
    (scalarSixChange e.hom X).mapIso
      (((upperStar (c.obj ell) a).mapDerivedCategorySingleFunctor 0).app
          (c.line ell s d) ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso (p.power d))

set_option maxHeartbeats 1600000 in
-- Native scalar-extension and module-pullback comparisons require nested derived reductions.
/-- Insert a point Tate-line section into a complex on X. The point morphism
is pulled back, followed by the root-normalized Tate comparison; the right
unitor fixes its ordinary unit normalization.
Source: pure-tensor comparison in proof Step 3
(blueprint: sk-thm-derived-duality). -/
def degreeTwistInsert (ell : ℕ) [Fact ell.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (c : PurityTransport.Coefficient ell)
    (e : c.bundled.{u} ell ≅ (⟨Λ⟩ : ScalarSixRing.{u}))
    {X s : Scheme.{u}} (a : X ⟶ s)
    (p : PurityTransport.LinePullCoordinates ell c a) (d : ℕ)
    (M : CohomologyTransport.D Λ X)
    (t : 𝟙_ (CohomologyTransport.D Λ s) ⟶ currentTwist ell Λ c e s d) :
    M ⟶ M ⊗ currentTwist ell Λ c e X d :=
  let unitPull : (scalarSixPull (⟨Λ⟩ : ScalarSixRing.{u}) a).obj (𝟙_ _) ≅ 𝟙_ _ :=
    ((leftDerivedUpperStarIsoMapDerivedCategory Λ a).symm.app _) ≪≫
      leftDerivedUpperStarUnitIso Λ a
  (ρ_ M).inv ≫ M ◁ (unitPull.inv ≫
    (scalarSixPull (⟨Λ⟩ : ScalarSixRing.{u}) a).map t ≫
      (degreeTwistPull ell Λ c e a p d).hom)

end AlgebraicGeometry.ProEtale.CondensedRing.Current
