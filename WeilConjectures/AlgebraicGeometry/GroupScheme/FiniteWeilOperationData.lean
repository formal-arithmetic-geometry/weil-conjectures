/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdmissibleCondensedCoefficientFamily
import WeilConjectures.DeligneLaumon.NativeWeilDerivedFramework
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ConstantWeil.CondensedConstantWeilTwist
import WeilConjectures.AlgebraicGeometry.Weil.WeilTensorProduct
import WeilConjectures.Compactification.Defs
import WeilConjectures.DeligneLaumon.NativeWeilDerivedFramework
import WeilConjectures.AlgebraicGeometry.Weil.WeilTensorProduct
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ExchangeProjection
import WeilConjectures.PoincareDuality.ProjectionFormula
public import WeilConjectures.SixFunctors.FrobeniusSquareExchange.FrobeniusSquareExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ModelSemilinearComparison.CondensedModelFrobeniusOperatorsBase
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.SixFunctors.OrdinaryModuleDerivedInternalHom
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteKInjectiveResolutionsMixedUniverses
public import WeilConjectures.CategoryTheory.SmoothPurity.QuasiIsoHomComplexMapMixedUniverses
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleObjectProjectionMap
public import WeilConjectures.CategoryTheory.ExactSectionsDerivedCup
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedCoefficientMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
public import WeilConjectures.AlgebraicGeometry.RootCoordinateFace.RootTowerCoordinateFace
public import Mathlib.CategoryTheory.Adjunction.Mates
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
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
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
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedScalarCoefficientMaps
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Shift
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
public import WeilConjectures.AlgebraicGeometry.PurityTransport.Transport
public import WeilConjectures.AlgebraicGeometry.Picard.Purity.Condensed.NativeCompactSupportWeilTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportCompositionData
public import WeilConjectures.AlgebraicGeometry.SepFinType
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompBaseChangeDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedFrobeniusComparisonCoherence
public import WeilConjectures.AlgebraicGeometry.PurityCoefficientChange.CondensedPurityCoefficientChange
public import WeilConjectures.SixFunctors.FiniteFieldDatum.FrobeniusSquareCartesian
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportLinePull
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportPull
public import WeilConjectures.AlgebraicGeometry.RationalP1.Tate.RationalTateLineComposition
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsComapUnit
public import WeilConjectures.Compactification.CommonDenseRefinement
public import Mathlib.CategoryTheory.Shift.Adjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom
public import WeilConjectures.AlgebraicGeometry.Native.NativeHomSourceShiftData
public import WeilConjectures.AlgebraicGeometry.Native.NativeDerivedHomSignedExact
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ExactScalarPointCup
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSmoothTraceUnit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.SitePerfectComplex
public import WeilConjectures.AlgebraicGeometry.Internal.InternalSignedTateTwist
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
public import Mathlib.Data.ZMod.Basic
import WeilConjectures.AlgebraicGeometry.PurityTransport.Coefficient.TransportCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteCoefficientEncodingDataSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteRestrictionEncodingSupplement
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportRoot
public import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
public import WeilConjectures.CategoryTheory.Constant.ConstantScalarRestrictionTensorSupplement
public import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportUnits
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonConstantGenerator
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalCompactSupportSiteComparison
public import WeilConjectures.AlgebraicGeometry.Geo.GeoP1Cohomology
public import WeilConjectures.AlgebraicGeometry.Sp.SpDirectImageEtaleMate
public import WeilConjectures.AlgebraicGeometry.ProjectiveLineTateCoefficientGenerator
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.CategoryTheory.InternalSectionModuleFlat
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalization
import Mathlib.Tactic.DefEqTransformations
import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarPullbackNormalization
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsFlat
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
import WeilConjectures.AlgebraicGeometry.QuotientTensorFlatModel.QuotientTensorLeftFlatComputation
import WeilConjectures.AlgebraicGeometry.QuotientTensorFlatModel.QuotientTensorRightFlatComputation
import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientScalarTensorCanonical
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PullIsoMonoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalBraided
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
import Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarPullbackSquareCoherence
import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalPullNormalizationExistence
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat
import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.ScalarPullbackMateInverseNormalized
import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances
public import WeilConjectures.AlgebraicGeometry.GroupScheme.CondensedFrobeniusTransport.CondensedFrobeniusCohomologyTransportIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntrinsicFiniteTorMixedSupportCup
public import Mathlib.Algebra.Category.ModuleCat.AB

/-! # Native data for finite and integral Weil operations

Source: latest blueprint, `lem-fix-weil-operations-finite`, statement and proof.
(blueprint: def-finite-weil-native-operation-data)

All operation arrows below are the native arrows, specialized to geometric fibres.
The compactification is the geometric fibre of a model compactification. In particular
its middle Frobenius and both exchange squares are determined by that model.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
-- Match the native site size used by derivedPoincarePairing.
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [local instance 10000] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology

universe u v w u₁ v₁

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilConjectures

/-- The strict-pair commuting-arrow equation.
Source: sk-def-sf-weil-complexes (blueprint: def-finite-weil-native-operation-data). -/
def finiteWeilIntertwines {A : Type u} [Category.{v} A]
    (P : A ⥤ A) {K L : A} (φK : P.obj K ≅ K) (φL : P.obj L ≅ L)
    (a : K ⟶ L) : Prop :=
  P.map a ≫ φL.hom = φK.hom ≫ a

/-- Alpha is exchange followed by direct image of the input datum.
This definition uses a specified transformation, without choosing an isomorphism.
Source: the displayed formula (blueprint: def-finite-weil-native-operation-data). -/
def finiteWeilAlpha {A : Type u} {B : Type w} [Category.{v} A] [Category.{v} B]
    {PX : A ⥤ A} {PY : B ⥤ B} (F : A ⥤ B)
    (e : F ⋙ PY ⟶ PX ⋙ F) {K : A} (φK : PX.obj K ≅ K) :
    PY.obj (F.obj K) ⟶ F.obj K :=
  e.app K ≫ F.map φK.hom

/-- Native derived-pullback coordinates on the recorded strict pair's datum.
Source: exact-to-derived comparison (blueprint: def-finite-weil-native-operation-data). -/
def finiteWeilStrictDatum
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}} (g : X ≅ X)
    (K : StrictWeilCondensed.Complex Λ g) :
    (moduleObjectDerivedPullback Λ g.hom).obj K.carrier.obj ≅ K.carrier.obj :=
  (leftDerivedUpperStarIsoMapDerivedCategory Λ g.hom).app K.carrier.obj ≪≫
    (ObjectProperty.ι _).mapIso K.str

/-- Native tensor datum, including the derived pullback tensorator.
Source: proof Step 5 (blueprint: def-finite-weil-native-operation-data). -/
def finiteWeilTensorDatum
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}} (g : X ⟶ X)
    {K L : CompactificationReindexing.D Λ X}
    (φK : (moduleObjectDerivedPullback Λ g).obj K ≅ K)
    (φL : (moduleObjectDerivedPullback Λ g).obj L ≅ L) :
    (moduleObjectDerivedPullback Λ g).obj (K ⊗ L) ≅ K ⊗ L :=
  ((leftDerivedUpperStarTensorIso Λ g).app K).app L ≪≫ tensorIso φK φL

/-- The internal-Hom datum, with the inverse in its contravariant slot.
Source: proof Step 5 (blueprint: def-finite-weil-native-operation-data). -/
def finiteWeilHomDatum
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}} (g : X ≅ X)
    {K L : CompactificationReindexing.D Λ X}
    (φK : (moduleObjectDerivedPullback Λ g.hom).obj K ≅ K)
    (φL : (moduleObjectDerivedPullback Λ g.hom).obj L ≅ L) :
    (moduleObjectDerivedPullback Λ g.hom).obj ((ihom K).obj L) ≅ (ihom K).obj L := by
  let P := moduleObjectDerivedPullback Λ g.hom
  letI : P.Monoidal := monoidal_leftDerivedUpperStar Λ g.hom
  have : P.IsEquivalence := by
    dsimp [P, moduleObjectDerivedPullback]
    infer_instance
  exact Functor.Monoidal.ihomObjIso P K L ≪≫
    (MonoidalClosed.internalHom.mapIso φK.symm.op).app (P.obj L) ≪≫
      (ihom K).mapIso φL

/-- Canonical restriction at the geometric point, before taking exact scalar sections.
Source: proof Step 8 (blueprint: def-finite-weil-native-operation-data). -/
def finiteWeilPointRestriction (D : FiniteFieldDatum.{u})
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :
    letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
    𝟭 (CompactificationReindexing.D Λ (Spec (.of D.k))) ≅
      moduleObjectDerivedPullback Λ (CondensedFrobeniusTransport.pointFrobenius D).hom :=
  letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  (leftDerivedUpperStarIsoMapDerivedCategory Λ
      (CondensedFrobeniusTransport.pointFrobenius D).hom ≪≫
    Functor.mapDerivedCategoryNatIso
      (upperStarIsoIdOfIsSepClosed Λ (CondensedFrobeniusTransport.pointFrobenius D).hom) ≪≫
    Functor.mapDerivedCategoryIdIso _).symm

/-- The scalar operator is sections of alpha after the canonical point restriction.
The generic sections parameter lets each occurrence use its own existing scalar category.
Source: the formula Fib(Rf(phi)) Fib(Ex) rho, Step 8
(blueprint: def-finite-weil-native-operation-data). -/
def finiteWeilPointOperator {A : Type u} {B : Type w} {E : Type u₁}
    [Category.{v} A] [Category.{v} B] [Category.{v₁} E]
    {PX : A ⥤ A} {PY : B ⥤ B} (S : B ⥤ E) (ρ : 𝟭 B ≅ PY)
    (F : A ⥤ B) (e : F ⋙ PY ⟶ PX ⋙ F) {K : A} (φK : PX.obj K ≅ K) :
    S.obj (F.obj K) ⟶ S.obj (F.obj K) :=
  S.map (ρ.hom.app (F.obj K) ≫ finiteWeilAlpha F e φK)

end WeilConjectures
