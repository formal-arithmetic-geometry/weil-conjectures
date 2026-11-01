/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOpenProper.CondensedOpenProperPasting
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedEtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarPullbackNormalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
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
public import Mathlib.CategoryTheory.Adjunction.Mates
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
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportProjectionFormula
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
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
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import WeilConjectures.AlgebraicGeometry.LocallyClosedExtensionData.LocallyClosedExtensionCoherence
public import WeilConjectures.CategoryTheory.AdjunctionSquareComposition
public import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarGeometricExchangeRectangle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenExtensionConstructibleFiniteTor
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientRefinement
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
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsFlat
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.CategoryTheory.MorphismProperty.Retract
public import WeilConjectures.CategoryTheory.DerivedCategory.SixFunctors.NativeInternalHomExact
public import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
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
public import WeilConjectures.CategoryTheory.SixFunctors.ContravariantIsoLocus
public import WeilConjectures.CategoryTheory.RingedSignedTensor.RingedTensorSignedCancellation
public import WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
public import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.SixFunctors.Coefficient.Tensor.CoefficientTensorCurryNormalization
public import WeilConjectures.CategoryTheory.Scalar.ScalarHomComparisonTower
public import WeilConjectures.Algebra.Homology.Derived.DerivedScalarExtensionCounitShift
public import WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Retract
public import WeilConjectures.CategoryTheory.Monoidal.Closed.IhomComparison
public import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory
public import WeilConjectures.SmoothPurity.Exceptional.ExceptionalAdjointAdmissibility
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityReductionTowerData
public import WeilConjectures.AlgebraicGeometry.Integral.Constant.IntegralConstantModelRealizationSupplement
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import WeilConjectures.AlgebraicGeometry.CondensedIntegralCriterion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.SitePerfectComplex
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleObjectProjectionMap
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionProjection
public import WeilConjectures.PoincareDuality.ProjectionFormula
public import WeilConjectures.AlgebraicGeometry.QuotientTensorFlatModel.QuotientTensorLeftFlatComputation
public import WeilConjectures.AlgebraicGeometry.QuotientTensorFlatModel.QuotientTensorRightFlatComputation
public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientScalarTensorCanonical
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PullIsoMonoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalBraided
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarPullbackSquareCoherence
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalPullNormalizationExistence
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat
public import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompBaseChangeDefs
public import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportCompositionData
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement

/-! # Native finite semilinear exchange coherence

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-package/
prop-pur-weil-equivariance-compatibilities.proof.md, constituent compatibility assembly.
(blueprint: lem-pur-isomorphism-finite-exchange-coherence).

All categories are ordinary unbounded internal-module derived categories. Scheme
isomorphisms in the base-change diagrams carry no ground-field linearity condition.
Positive quotient exponents are written n+1, so n=0 includes the first quotient.
The retained fixed-scalar origin is transported by its normalized section-action encoding.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
open AlgebraicGeometry WeilConjectures

namespace AlgebraicGeometry.ProEtale.CondensedRing.NativeFiniteExchange

open CompactificationReindexing

/-- The existing finite discrete condensed coefficient, at any positive exponent.
Source: def-pur-conventions, finite coefficient convention
(blueprint: lem-pur-isomorphism-finite-exchange-coherence). -/
abbrev coefficient (P : PurityFiniteSetting.{u}) (n : ℕ) :=
  DerivedNakayama.quotientRing P.coefficients.l P.extension (n + 1)

/-- Commutativity of the actual finite quotient, read in its spectral-topology model.
Source: def-pur-conventions, finite discrete condensed coefficients
(blueprint: lem-pur-isomorphism-finite-exchange-coherence). -/
instance coefficientComm (P : PurityFiniteSetting.{u}) (n : ℕ) :
    IsCommMonObj (coefficient P n) :=
  letI := (Padic.coefficientExtensionAbsoluteValue P.coefficients.l P.extension).toNormedField
  Profinite.isCommMonObj_continuousCoefficientRingObj
    (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

set_option maxHeartbeats 1600000 in
-- Native derived-functor endpoint comparisons need this elaboration allowance.
/-- Compose the supplied proper/open models without requiring a dense middle open.
Source: the node's composition diagram, tf=(qr)(bj)
(blueprint: lem-pur-isomorphism-finite-exchange-coherence). -/
def composite {X Y Z : Scheme.{u}} {f : X ⟶ Y} {t : Y ⟶ Z}
    (c : Compactification f) (d : Compactification t)
    (b : Compactification (c.g ≫ d.i)) : Compactification (f ≫ t) where
  Z := b.Z
  i := c.i ≫ b.i
  g := b.g ≫ d.g
  comm := calc
    f ≫ t = (c.i ≫ c.g) ≫ (d.i ≫ d.g) := congrArg₂ (fun x y ↦ x ≫ y) c.comm d.comm
    _ = c.i ≫ ((c.g ≫ d.i) ≫ d.g) := by simp only [Category.assoc]
    _ = c.i ≫ ((b.i ≫ b.g) ≫ d.g) := congrArg (fun h ↦ c.i ≫ (h ≫ d.g)) b.comm
    _ = (c.i ≫ b.i) ≫ (b.g ≫ d.g) := by simp only [Category.assoc]
  isOpenImmersion := inferInstance
  isProper := inferInstance

set_option maxHeartbeats 1600000 in
-- Native derived-functor endpoint comparisons need this elaboration allowance.
/-- D=P_q Gamma_Q J_j, with the actual open-adjunction Gamma and canonical compositors.
The units parameter is normalized data, not an arbitrary comparison.
Source: lem-zl-condensed-open-proper-pasting(b), composition diagram
(blueprint: lem-pur-isomorphism-finite-exchange-coherence). -/
def composition (units : CondensedOpenProper.OpenUnits Λ)
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {t : Y ⟶ Z}
    (c : Compactification f) (d : Compactification t)
    (b : Compactification (c.g ≫ d.i)) (K : D Λ X) :
    (F Λ d).obj ((F Λ c).obj K) ⟶ (F Λ (composite c d b)).obj K :=
  (R Λ d.g).map
      ((CondensedOpenProper.gamma Λ units (CommSq.mk b.comm.symm)).app ((J Λ c.i).obj K)) ≫
    (rightDerivedLowerStarComp Λ b.g d.g).hom.app
      ((J Λ b.i).obj ((J Λ c.i).obj K)) ≫
    (R Λ (b.g ≫ d.g)).map
      ((CompactSupportComposition.openComp Λ c.i b.i).hom.app K)

set_option maxHeartbeats 1600000 in
-- Native derived-functor endpoint comparisons need this elaboration allowance.
/-- A pulled-back composition diagram, retaining the three compactification squares
and both central faces. These faces specify pullback of the entire supplied diagram.
Source: the node's base-changed proper/open composition diagram
(blueprint: lem-pur-isomorphism-finite-exchange-coherence). -/
structure DiagramSquare {X Y Z X' Y' Z' : Scheme.{u}}
    {f : X ⟶ Y} {t : Y ⟶ Z} {f' : X' ⟶ Y'} {t' : Y' ⟶ Z'}
    (c : Compactification f) (d : Compactification t)
    (b : Compactification (c.g ≫ d.i))
    (c' : Compactification f') (d' : Compactification t')
    (b' : Compactification (c'.g ≫ d'.i))
    (a : X' ⟶ X) (v : Y' ⟶ Y) (w : Z' ⟶ Z) where
  first : Square c c' a v
  second : Square d d' v w
  total : Square (composite c d b) (composite c' d' b') a w
  middleOpen : IsPullback first.middle b'.i b.i total.middle
  middleProper : CommSq total.middle b'.g b.g second.middle

set_option maxHeartbeats 1600000 in
-- Native derived-functor endpoint comparisons need this elaboration allowance.
/-- Chi is the inverse of the recorded normalized scalar/pullback map, with the
native pullback name exposed by unfolding its alias, not by a new choice.
Source: the node's definition of chi
(blueprint: lem-pur-isomorphism-finite-exchange-coherence). -/
def chi
    {Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]
    (b : ∀ {U V : Scheme.{u}} (h : U ⟶ V),
      QuotientChange.D a V ⋙ QuotientChange.L Λ' h ≅
        QuotientChange.L Λ h ⋙ QuotientChange.D a U)
    {U V : Scheme.{u}} (h : U ⟶ V) :
    P Λ h ⋙ QuotientChange.D a U ≅ QuotientChange.D a V ⋙ P Λ' h := by
  unfold QuotientChange.L moduleObjectDerivedPullback at b
  exact (b h).symm

set_option maxHeartbeats 1600000 in
-- Native derived-functor endpoint comparisons need this elaboration allowance.
/-- The native open scalar isomorphism with the recorded scalar-extension alias.
Source: def-sfb-derived-open-immersion-shriek-iso, unit-normalized scalar comparison
(blueprint: lem-pur-isomorphism-finite-exchange-coherence). -/
def delta
    {Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]
    {U W : Scheme.{u}} (j : U ⟶ W) [IsOpenImmersion j] :
    J Λ j ⋙ QuotientChange.D a W ≅ QuotientChange.D a U ⋙ J Λ' j := by
  unfold QuotientChange.D QuotientChange.extension
  exact derivedOpenImmersionShriekIso a j

set_option maxHeartbeats 1600000 in
-- Native derived-functor endpoint comparisons need this elaboration allowance.
/-- The actual geometric-adjunction scalar mate with the native direct-image name.
Source: the node's definition of rho
(blueprint: lem-pur-isomorphism-finite-exchange-coherence). -/
def properScalar
    {Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]
    (b : ∀ {U V : Scheme.{u}} (h : U ⟶ V),
      QuotientChange.D a V ⋙ QuotientChange.L Λ' h ≅
        QuotientChange.L Λ h ⋙ QuotientChange.D a U)
    {U V : Scheme.{u}} (h : U ⟶ V) :
    R Λ h ⋙ QuotientChange.D a V ⟶ QuotientChange.D a U ⋙ R Λ' h := by
  have r := QuotientChange.rho a h (b h)
  unfold QuotientChange.F moduleObjectDerivedPushforward at r
  exact r

set_option maxHeartbeats 1600000 in
-- Native derived-functor endpoint comparisons need this elaboration allowance.
/-- The chosen-compactification coefficient map is the proper scalar mate followed
by the actual normalized open scalar comparison. No proper mate is inverted.
Source: the node's formula for kappa; internal-scalar-pullback normalization
(blueprint: lem-pur-isomorphism-finite-exchange-coherence). -/
def scalarComparison
    {Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]
    (b : ∀ {U V : Scheme.{u}} (h : U ⟶ V),
      QuotientChange.D a V ⋙ QuotientChange.L Λ' h ≅
        QuotientChange.L Λ h ⋙ QuotientChange.D a U)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (K : D Λ X) :
    (QuotientChange.D a Y).obj ((F Λ c).obj K) ⟶
      (F Λ' c).obj ((QuotientChange.D a X).obj K) :=
  (properScalar Λ a b c.g).app ((J Λ c.i).obj K) ≫
    (R Λ' c.g).map ((delta Λ a c.i).hom.app K)

set_option maxHeartbeats 1600000 in
-- Native derived-functor endpoint comparisons need this elaboration allowance.
/-- Identity and successive-isomorphism pasting of the specified exchange, on
ambient inputs, with the native pullback compositors displayed.
Source: the node, first two equations
(blueprint: lem-pur-isomorphism-finite-exchange-coherence). -/
structure HorizontalLaws (k : Type u) [Field k] : Prop where
  identity : ∀ {X Y : SepFinType k} (f : X ⟶ Y) (c : Compactification f.hom.left)
    (s : Square c c (𝟙 X.obj.left) (𝟙 Y.obj.left))
    (_h : s.middle = 𝟙 c.Z) (K : D Λ X.obj.left),
    (squareExchange Λ s).app K ≫
        (F Λ c).map ((leftDerivedUpperStarId Λ X.obj.left).hom.app K) =
      (leftDerivedUpperStarId Λ Y.obj.left).hom.app ((F Λ c).obj K)
  horizontal : ∀ {X Y : SepFinType k} (f : X ⟶ Y)
    {X' Y' X'' Y'' : Scheme.{u}} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
    (c : Compactification f.hom.left) (c' : Compactification f')
    (c'' : Compactification f'')
    {a : X' ⟶ X.obj.left} {v : Y' ⟶ Y.obj.left}
    {a' : X'' ⟶ X'} {v' : Y'' ⟶ Y'}
    [IsIso a] [IsIso v] [IsIso a'] [IsIso v']
    (s : Square c c' a v) (s' : Square c' c'' a' v')
    [IsIso s.middle] [IsIso s'.middle]
    (outer : Square c c'' (a' ≫ a) (v' ≫ v))
    (_h : outer.middle = s'.middle ≫ s.middle) (K : D Λ X.obj.left),
    (leftDerivedUpperStarComp Λ v' v).hom.app ((F Λ c).obj K) ≫
        (P Λ v').map ((squareExchange Λ s).app K) ≫
        (squareExchange Λ s').app ((P Λ a).obj K) =
      (squareExchange Λ outer).app K ≫
        (F Λ c'').map ((leftDerivedUpperStarComp Λ a' a).hom.app K)

set_option maxHeartbeats 1600000 in
-- Native derived-functor endpoint comparisons need this elaboration allowance.
/-- Exchange commutes with D on the full ambient category. The diagrams are
isomorphisms of underlying schemes, and neither their maps nor the induced
k-structures are required to respect the original ground field.
Source: the node, vertical composition equation
(blueprint: lem-pur-isomorphism-finite-exchange-coherence). -/
def VerticalLaw (k : Type u) [Field k] : Prop :=
  ∀ (units : CondensedOpenProper.OpenUnits Λ)
    {X Y Z : SepFinType k} (f : X ⟶ Y) (t : Y ⟶ Z)
    {X' Y' Z' : Scheme.{u}} {f' : X' ⟶ Y'} {t' : Y' ⟶ Z'}
    (c : Compactification f.hom.left) (d : Compactification t.hom.left)
    (b : Compactification (c.g ≫ d.i))
    (c' : Compactification f') (d' : Compactification t')
    (b' : Compactification (c'.g ≫ d'.i))
    {a : X' ⟶ X.obj.left} {v : Y' ⟶ Y.obj.left} {w : Z' ⟶ Z.obj.left}
    [IsIso a] [IsIso v] [IsIso w]
    (s : DiagramSquare c d b c' d' b' a v w)
    [IsIso s.first.middle] [IsIso s.second.middle] [IsIso s.total.middle]
    (K : D Λ X.obj.left),
    (P Λ w).map (composition Λ units c d b K) ≫
        (squareExchange Λ s.total).app K =
      (squareExchange Λ s.second).app ((F Λ c).obj K) ≫
        (F Λ d').map ((squareExchange Λ s.first).app K) ≫
        composition Λ units c' d' b' ((P Λ a).obj K)

set_option maxHeartbeats 1600000 in
-- Native derived-functor endpoint comparisons need this elaboration allowance.
/-- Agreement with the native composition isomorphism, for every coherent native
comparison datum, at every finite-Tor object in its localizing domain.
Source: sk-thm-sf-comp-composition, normalization of the middle interchange
(blueprint: lem-pur-isomorphism-finite-exchange-coherence). -/
def NativeCompositionLaw (k : Type u) [Field k] : Prop :=
  (∀ (X : SepFinType k) (K : D Λ X.obj.left),
    condensedConstructibleFiniteTor Λ X.obj.left K →
      localizingClosureProEtale Λ X.obj.left K) ∧
  ∀ (units : CondensedOpenProper.OpenUnits Λ)
    (H : CompactSupportComposition.CoherentData Λ k)
    {X Y Z : SepFinType k} (f : X ⟶ Y) (t : Y ⟶ Z)
    (c : Compactification f.hom.left) (d : Compactification t.hom.left)
    (b : Compactification (c.g ≫ d.i))
    (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory),
    condensedConstructibleFiniteTor Λ X.obj.left K.obj →
      composition Λ units c d b K.obj =
        (H.comp f t c d (composite c d b)).hom.app K

set_option maxHeartbeats 1600000 in
-- Native derived-functor endpoint comparisons need this elaboration allowance.
/-- Invertibility at precisely the retained bounded-below etale-origin inputs.
The fixed-scalar witness is that of the recorded dependency, transported through
its normalized section-action equivalence; no constructibility is imposed.
Source: the node's bounded-below finite etale-origin clause
(blueprint: lem-pur-isomorphism-finite-exchange-coherence). -/
def OriginCompositionLaw (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] (k : Type u) [Field k] : Prop :=
  ∀ (units : CondensedOpenProper.OpenUnits (FiniteDiscreteOrdinary.coefficient A))
    {X Y Z : SepFinType k} (f : X ⟶ Y) (t : Y ⟶ Z)
    (c : Compactification f.hom.left) (d : Compactification t.hom.left)
    (b : Compactification (c.g ≫ d.i))
    (K : D (FiniteDiscreteOrdinary.coefficient A) X.obj.left)
    (e : FiniteDiscreteOrdinary.Encoding A X.obj.left)
    (L : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X.obj.left)
      (ModuleCat.{u + 1} (ULift.{u + 1} A))))
    (_origin : Scheme.FixedEtaleOriginWitness X.obj.left (ULift.{u + 1} A) L)
    (_identification : e.fixedDerived.functor.obj K ≅ L.obj),
    IsIso (composition (FiniteDiscreteOrdinary.coefficient A) units c d b K)

set_option maxHeartbeats 1600000 in
-- Native derived-functor endpoint comparisons need this elaboration allowance.
/-- The origin clause in precisely the finite quotient's native spectral quotient topology.
The type is the same fixed-ring witness after the canonical section-action encoding.
Source: def-pur-conventions, coefficient and origin conventions
(blueprint: lem-pur-isomorphism-finite-exchange-coherence). -/
def finiteOriginCompositionLaw (P : PurityFiniteSetting.{u}) (n : ℕ) : Prop :=
  letI := (Padic.coefficientExtensionAbsoluteValue P.coefficients.l P.extension).toNormedField
  OriginCompositionLaw
    (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1)) P.field.k

variable {Λ}

/-- Commutativity already carried by a bundled coefficient object.
Source: the node's commutative coefficient convention
(blueprint: lem-pur-isomorphism-finite-exchange-coherence). -/
instance bundledComm (A : ScalarSixRing.{u}) : IsCommMonObj A.X := A.comm

/-- Read the same bundled commutativity through the monoid projection used by its maps.
Source: the node's commutative coefficient convention
(blueprint: lem-pur-isomorphism-finite-exchange-coherence). -/
instance bundledToMonComm (A : ScalarSixRing.{u}) : IsCommMonObj A.toMon.X := by
  change IsCommMonObj A.X
  exact A.comm

/-- Multiplicativity already carried by a bundled coefficient morphism.
Source: the node's actual quotient coefficient map
(blueprint: lem-pur-isomorphism-finite-exchange-coherence). -/
instance bundledMap_isMonHom {A B : ScalarSixRing.{u}} (a : A ⟶ B) :
    IsMonHom a.hom.hom := a.hom.isMonHom_hom

set_option maxHeartbeats 1600000 in
-- Native derived-functor endpoint comparisons need this elaboration allowance.
/-- The complete scalar square, including its proper and open constituents, for
an actual coefficient map. The inverse b is chi, and rho is its geometric mate.
Source: the node's quotient equation and its final constituent-normalization sentence
(blueprint: lem-pur-isomorphism-finite-exchange-coherence). -/
def ScalarLaw
    {Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]
    (b : ∀ {U V : Scheme.{u}} (h : U ⟶ V),
      QuotientChange.D a V ⋙ QuotientChange.L Λ' h ≅
        QuotientChange.L Λ h ⋙ QuotientChange.D a U)
    (k : Type u) [Field k] : Prop :=
  (∀ {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {v : Y' ⟶ Y} {w : X' ⟶ X} [IsIso v] [IsIso w]
    (s : ChosenCartesianSquare w f' f v) (K : D Λ X),
    QuotientChange.scalarExchangeLeft a s b K =
      QuotientChange.scalarExchangeRight a s b K) ∧
  (∀ {U W U' W' : Scheme.{u}} {j : U ⟶ W} {j' : U' ⟶ W'}
    [IsOpenImmersion j] [IsOpenImmersion j']
    {v : W' ⟶ W} {w : U' ⟶ U} [IsIso v] [IsIso w]
    (s : IsPullback w j' j v) (K : D Λ U),
    (QuotientChange.D a W').map ((beta Λ s).hom.app K) ≫
        (delta Λ a j').hom.app ((P Λ w).obj K) ≫
        (J Λ' j').map ((chi Λ a b w).hom.app K) =
      (chi Λ a b v).hom.app ((J Λ j).obj K) ≫
        (P Λ' v).map ((delta Λ a j).hom.app K) ≫
        (beta Λ' s).hom.app ((QuotientChange.D a U).obj K)) ∧
  ∀ {X Y : SepFinType k} (f : X ⟶ Y)
    {X' Y' : Scheme.{u}} {f' : X' ⟶ Y'}
    (c : Compactification f.hom.left) (c' : Compactification f')
    {v : Y' ⟶ Y.obj.left} {w : X' ⟶ X.obj.left} [IsIso v] [IsIso w]
    (s : Square c c' w v) [IsIso s.middle] (K : D Λ X.obj.left),
    condensedConstructibleFiniteTor Λ X.obj.left K →
      (QuotientChange.D a Y').map ((squareExchange Λ s).app K) ≫
          scalarComparison Λ a b c' ((P Λ w).obj K) ≫
          (F Λ' c').map ((chi Λ a b w).hom.app K) =
        (chi Λ a b v).hom.app ((F Λ c).obj K) ≫
          (P Λ' v).map (scalarComparison Λ a b c K) ≫
          (squareExchange Λ' s).app ((QuotientChange.D a X.obj.left).obj K)

set_option maxHeartbeats 1600000 in
-- Expose the two published names of derived scalar extension explicitly.
/-- The recorded compact-support scalar map, in the native scalar-extension notation.
Only the aliases for scalar extension and ordinary direct image are unfolded.
Source: lem-fix-operation-reduction, actual compactification coefficient comparison
(blueprint: lem-pur-isomorphism-finite-exchange-coherence). -/
def recordedScalarComparison {A B : ScalarSixRing.{u}} (a : A ⟶ B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (K : D A.X X) :
    (QuotientChange.D a.hom.hom Y).obj ((F A.X c).obj K) ⟶
      (F B.X c).obj ((QuotientChange.D a.hom.hom X).obj K) := by
  unfold QuotientChange.D QuotientChange.extension
  have r := (scalarCompactSupportMap a c.i c.g).app K
  unfold scalarSixChange scalarSixAdjunctionLeft RootCoordinateFace.lower
    moduleObjectDerivedPushforward at r
  exact r

set_option maxHeartbeats 1600000 in
-- Native derived-functor endpoint comparisons need this elaboration allowance.
/-- Finite-quotient scalar comparisons are isomorphisms on the intrinsic finite-Tor
constructible subcategory and equal the recorded compact-support coefficient map.
Source: lem-fix-operation-reduction, finite quotient clause
(blueprint: lem-pur-isomorphism-finite-exchange-coherence). -/
def ScalarIdentification {A B : ScalarSixRing.{u}} (a : A ⟶ B)
    [IsMonHom a.hom.hom]
    (b : ∀ {U V : Scheme.{u}} (h : U ⟶ V),
      QuotientChange.D a.hom.hom V ⋙ QuotientChange.L B.X h ≅
        QuotientChange.L A.X h ⋙ QuotientChange.D a.hom.hom U)
    (k : Type u) [Field k] : Prop :=
  ∀ {X Y : SepFinType k} (f : X ⟶ Y) (c : Compactification f.hom.left)
    (K : D A.X X.obj.left), condensedConstructibleFiniteTor A.X X.obj.left K →
      IsIso (scalarComparison A.X a.hom.hom b c K) ∧
        scalarComparison A.X a.hom.hom b c K = recordedScalarComparison a c K

set_option maxHeartbeats 1600000 in
-- Native derived-functor endpoint comparisons need this elaboration allowance.
/-- Ambient normalized pasting and finite-origin invertibility for the native finite
exchange. The n=0 instance means A_1; there is no zero-level omission.
Source: latest blueprint constituent assembly, expanded as the node's proof steps 1--4
(blueprint: lem-pur-isomorphism-finite-exchange-coherence).

Proof: identify finite discrete internal modules with constant section modules by
exact normalized equivalences, preserving the geometric and open units and counits.
For identities apply identity mate pasting and the normalized open identity. For
successive base maps expand exchange into its proper mate and open beta; mate pasting
and open pasting give the two factors, and naturality interchanges the middle maps.
For composition apply the open/proper base-change cube to Gamma, whisker by J_j and
P_q, and use proper mate pasting and the open compositor. This is the displayed ambient
vertical equation. On the native finite-Tor subcategory, the open-adjunction transpose
of Gamma is inverse lambda, hence the identity-on-the-open normalized interchange.
The native composition law therefore gives the same D, including nondense models by
passing through the closure and the canonical refinement. For a retained bounded-below
etale origin, extend its antecedent by etale j_!. The finite constant transport and
single-level proper/open transport identify the central Gamma with the etale clopen
comparison: their open-adjunction transposes are both inverse lambda. The latter is
invertible, and the outer proper images and compositors preserve its inverse. Repeat
this argument for the entire primed diagram. No tower is constructed or evaluated. -/
theorem finiteExchangeCoherence (P : PurityFiniteSetting.{u}) (n : ℕ) :
    HorizontalLaws (coefficient P n) P.field.k ∧
      VerticalLaw (coefficient P n) P.field.k ∧
      NativeCompositionLaw (coefficient P n) P.field.k ∧
      finiteOriginCompositionLaw P n := by
  sorry

set_option maxHeartbeats 1600000 in
-- Native derived-functor endpoint comparisons need this elaboration allowance.
/-- Quotient coefficient coherence for the specified normalized maps, including
both ambient constituent equations and finite-Tor invertibility of kappa.
Source: latest blueprint lem-fix-operation-reduction.proof.md, final paragraph;
node proof steps 5--7 (blueprint: lem-pur-isomorphism-finite-exchange-coherence).

Proof: the normalized scalar/pullback maps satisfy the geometric composition cube.
Apply the scalar/geometric exchange rectangle to the proper square; its rho factors
are the actual geometric-adjunction mates. Compose with inverse balancing maps to put
it in the chi orientation. No rho is inverted. For the open factor transpose through
the open adjunctions. The open scalar comparison and beta are fixed by their units,
so after cancellation both transposes are the same scalar/pullback cube. Full
faithfulness of open extension gives the ambient open equation. Substitute these two
identities into exchange=(proper image of beta)(proper exchange) and
kappa=(proper image of delta)(rho at j_!). Naturality of rho moves it past beta, giving
the displayed quotient square. The finite coefficient part of operation reduction
identifies this factorwise map with its specified compact-support scalar comparison
and makes it invertible on the constructible finite-Tor domain. The argument includes
equal exponents, nonflat quotient maps, empty schemes and arbitrary unbounded ambient
inputs for the constituent equations, and imposes no ground-field linearity. -/
theorem finiteCoefficientCoherence (P : PurityFiniteSetting.{u})
    (n m : ℕ) (hmn : m ≤ n)
    (b : ∀ {U V : Scheme.{u}} (h : U ⟶ V),
      QuotientChange.D
          (basicOperationsFiniteReduction P.coefficients.l P.extension n m hmn).hom.hom V ⋙
        QuotientChange.L (coefficient P m) h ≅
      QuotientChange.L (coefficient P n) h ⋙
        QuotientChange.D
          (basicOperationsFiniteReduction P.coefficients.l P.extension n m hmn).hom.hom U)
    (_normalized : ∀ {U V : Scheme.{u}} (h : U ⟶ V),
      QuotientChange.PullNormalized
        (basicOperationsFiniteReduction P.coefficients.l P.extension n m hmn).hom.hom h (b h)) :
    ScalarLaw
        (basicOperationsFiniteReduction P.coefficients.l P.extension n m hmn).hom.hom b P.field.k ∧
      ScalarIdentification
        (basicOperationsFiniteReduction P.coefficients.l P.extension n m hmn) b P.field.k := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.NativeFiniteExchange
