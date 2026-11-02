/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
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
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import WeilConjectures.CategoryTheory.DerivedCategory.SixFunctors.NativeInternalHomExact
public import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory
public import Mathlib.AlgebraicGeometry.Noetherian
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
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedCoefficientUnit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedVerdierExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedCoefficientMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
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
public import WeilConjectures.AlgebraicGeometry.Locally.LocallyPerfectScalarModel
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
public import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorComparison
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalization
public import WeilConjectures.PoincareDuality.ProjectionFormula
public import Mathlib.Tactic.DefEqTransformations
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarPullbackNormalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleObjectProjectionMap
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsFlat
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionProjection
public import WeilConjectures.AlgebraicGeometry.QuotientTensorFlatModel.QuotientTensorLeftFlatComputation
public import WeilConjectures.AlgebraicGeometry.QuotientTensorFlatModel.QuotientTensorRightFlatComputation
public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientScalarTensorCanonical
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PullIsoMonoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalBraided
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarPullbackSquareCoherence
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalPullNormalizationExistence
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat
public import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.ScalarPullbackMateInverseNormalized
public import WeilConjectures.AlgebraicGeometry.FiniteRestriction.FiniteRestrictionNormalizedAdjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingMap
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Native finite exceptional constructions

Source: latest blueprint, lem-coef-finite-exceptional.proof.md, paragraphs 1--2
(blueprint: def-sf-finite-exceptional-constructions).

Indices are predecessors of positive coefficient exponents. The coefficients are the
actual quotients of the integers of E. All functors have ordinary native module-object
endpoints. The encoding inputs are the dependency's normalized section-action encodings.
The two choices below are from uniquely normalized adjunctions and dual formulas.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme Opposite
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
open scoped CategoryTheory.Obj CategoryTheory.Functor MonoidalCategory

namespace WeilConjectures.NativeFiniteExceptional

variable (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
  [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]

/-- The actual positive coefficient quotient. Source: the coefficient convention
(blueprint: def-sf-finite-exceptional-constructions). -/
abbrev Ring (n : ℕ) := Padic.coefficientExtensionRing ell E (n + 1)

local instance (n : ℕ) : TopologicalSpace (Ring ell E n) := ⊥
local instance (n : ℕ) : DiscreteTopology (Ring ell E n) := ⟨rfl⟩
local instance (n : ℕ) : IsTopologicalRing (Ring ell E n) := inferInstance
local instance (n : ℕ) : Finite (Ring ell E n) :=
  Padic.finite_coefficientExtensionRing ell E (n + 1) (Nat.succ_pos n)

/-- The discrete quotient as its actual condensed ring. Source: finite coefficients
(blueprint: def-sf-finite-exceptional-constructions). -/
def coefficient (n : ℕ) : ScalarSixRing.{u} :=
  ⟨AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary.coefficient (Ring ell E n)⟩

/-- The quotient factor map, including equal indices. Source: quotient reduction
(blueprint: def-sf-finite-exceptional-constructions). -/
def quotient {m n : ℕ} (h : n ≤ m) : Ring ell E m →+* Ring ell E n :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))

/-- Postcomposition by the quotient map on continuous functions. Source: the actual
coefficient homomorphism (blueprint: def-sf-finite-exceptional-constructions). -/
def quotientRingSheafMap {m n : ℕ} (h : n ≤ m) :
    Profinite.continuousCoefficientRingSheaf (Ring ell E m) ⟶
      Profinite.continuousCoefficientRingSheaf (Ring ell E n) :=
  Profinite.continuousMapRingSheafMapOfUniverse (quotient ell E h)
    continuous_of_discreteTopology

/-- The same quotient as a map of condensed commutative rings. Source: quotient
coefficients (blueprint: def-sf-finite-exceptional-constructions). -/
def quotientScalar {m n : ℕ} (h : n ≤ m) : coefficient ell E m ⟶ coefficient ell E n :=
  ⟨⟨(sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (quotientRingSheafMap ell E h)⟩⟩

/-- The recorded full finite-Tor domain. Source: def-weil-finite-tor-amplitude
(blueprint: def-sf-finite-exceptional-constructions). -/
abbrev domain (T : Scheme.{u}) (n : ℕ) :=
  condensedConstructibleFiniteTor (coefficient ell E n).X T

/-- Ordinary derived quotient extension, without any completion. Source: Q_T
(blueprint: def-sf-finite-exceptional-constructions). -/
abbrev reduction (T : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :=
  scalarSixChange (quotientScalar ell E h) T

/-- Quotient extension preserves the specified full domain. Source: paragraph 2
(blueprint: def-sf-finite-exceptional-constructions).
Proof: the finite-ring coefficient equivalence identifies the native relative tensor
with ordinary quotient tensor. A bounded flat model stays flat with the same bounds;
finite locally constant models on the same strata remain finite constant models.
This proves both bounded constructibility and the unchanged finite Tor interval. -/
theorem reduction_preserves (T : Scheme.{u}) {m n : ℕ} (h : n ≤ m)
    (K : (domain ell E T m).FullSubcategory) :
    domain ell E T n ((reduction ell E T h).obj K.obj) := by
  sorry

/-- The literal full-subcategory restriction of quotient extension. Source: Q_T
(blueprint: def-sf-finite-exceptional-constructions). -/
def Q (T : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    (domain ell E T m).FullSubcategory ⥤ (domain ell E T n).FullSubcategory :=
  (domain ell E T n).lift ((domain ell E T m).ι ⋙ reduction ell E T h)
    (reduction_preserves ell E T h)

/-- The finite quotient is an admissible coefficient. Source: finite coefficients
(blueprint: def-sf-finite-exceptional-constructions).
Proof: its residue ring is finite and its maximal ideal is nilpotent. Since ell lies
in that ideal, an ell-power annihilates the quotient. Shrink the finite discrete ring
to Type 0; postcomposition by the ring equivalence gives the prescribed coefficient
presentation required by IsLocalizingAdmissibleCoefficient. -/
theorem coefficient_admissible (n : ℕ) :
    IsLocalizingAdmissibleCoefficient ell (coefficient ell E n).X := by
  sorry

variable (D : FiniteFieldDatum.{u}) (hell : ell ≠ D.p)

/-- The characteristic already determined by the global finite-field datum.
Source: the standing finite-field convention
(blueprint: def-sf-finite-exceptional-constructions).
Proof: cardinality q = p^a gives characteristic p on k0; its injective algebra map
into the fixed algebraic closure gives the same characteristic on k. -/
theorem characteristic : ringChar D.k = D.p := by
  sorry

local instance : Fact (ringChar D.k).Prime := ⟨by
  rw [characteristic D]
  exact D.prime⟩

/-- The standing inequality ell ≠ p, read in the geometric field.
Source: the standing coefficient convention
(blueprint: def-sf-finite-exceptional-constructions).
Proof: substitute characteristic(D.k)=D.p and use the symmetric prime inequality. -/
theorem charDifferent (hell : ell ≠ D.p) : ringChar D.k ≠ ell := by
  sorry

include hell in
/-- The field-CD witness derived from the fixed algebraic closure.
Source: paragraph 1 (blueprint: def-sf-finite-exceptional-constructions).
Proof: the fixed closure is algebraically closed. Apply BaseFieldFiniteCD.of_isAlgClosed
using the characteristic inequality obtained from the fixed finite-field datum. -/
theorem fieldCD : BaseFieldFiniteCD ell D.k := by
  sorry

variable {X Y : Over (Spec (.of D.k))}
  [Xft : LocallyOfFiniteType X.hom] [Xqc : QuasiCompact X.hom] [Xsep : IsSeparated X.hom]
  [Yft : LocallyOfFiniteType Y.hom] [Yqc : QuasiCompact Y.hom] [Ysep : IsSeparated Y.hom]
  (f : X ⟶ Y) [fsep : IsSeparated f.left]
  [fft : LocallyOfFiniteType f.left] [fqc : QuasiCompact f.left]
  (c : Compactification f.left)
  (encoding : ∀ (n : ℕ) (T : Scheme.{u}), Encoding (Ring ell E n) T)

local instance : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom

local instance (n : ℕ) :
    (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (ULift.{u + 1} (Ring ell E n))) c).IsLeftAdjoint :=
  Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification
    (ULift.{u + 1} (Ring ell E n)) c

/-- The finite native constructibility predicates agree. Source: finite coefficient
identification in paragraph 1 (blueprint: def-sf-finite-exceptional-constructions).
Proof: the normalized section-action equivalence identifies local finite presentations
with constant finite modules after a pro-etale cover. Over a finite ring finite modules
are finitely presented. Apply on the same locally closed strata, degree by degree;
boundedness and every relative tensor test are unchanged. -/
theorem domain_eq (T : Over (Spec (.of D.k)))
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom] (n : ℕ) :
    domain ell E T.left n = constantModelBoundedConstructible (coefficient ell E n).X T.left ⊓
      _root_.DerivedCategory.finiteTorAmplitude _ := by
  sorry

include hell Xft Xqc Xsep Yft Yqc Ysep fsep fft fqc in
/-- Membership-only preservation certificates for the actual two functors.
Source: thm-sf-preservation-class and paragraph 1
(blueprint: def-sf-finite-exceptional-constructions).
Proof: finite exceptional preservation gives the right-hand certificate in fixed scalar
coordinates; the exact normalized encoding preserves and reflects constructibility and
every Tor interval. Proper finite-coefficient finiteness and exact extension by zero give
the left-hand certificate. No right adjoint is assumed on the entire native category. -/
theorem operations_preserve (n : ℕ) :
    (∀ K : (domain ell E X.left n).FullSubcategory,
      domain ell E Y.left n
        ((FiniteRestriction.support (Ring ell E n) c).obj K.obj)) ∧
    (∀ L : (domain ell E Y.left n).FullSubcategory,
      domain ell E X.left n
        ((FiniteRestriction.conjugate (Ring ell E n) (encoding n)
          (sfFiniteExceptionalAt (ULift.{u + 1} (Ring ell E n)) c)).obj L.obj)) := by
  sorry

/-- Compact support restricted to the full finite-Tor domains. Source: paragraph 1
(blueprint: def-sf-finite-exceptional-constructions). -/
def F (n : ℕ) :
    (domain ell E X.left n).FullSubcategory ⥤ (domain ell E Y.left n).FullSubcategory :=
  (domain ell E Y.left n).lift ((domain ell E X.left n).ι ⋙
    FiniteRestriction.support (Ring ell E n) c)
    (operations_preserve ell E D hell f c encoding n).1

/-- The existing finite exceptional comparison composite in native coefficients.
Source: def-weil-exceptional-inverse-image and paragraph 1
(blueprint: def-sf-finite-exceptional-constructions). -/
def G (n : ℕ) :
    (domain ell E Y.left n).FullSubcategory ⥤ (domain ell E X.left n).FullSubcategory :=
  (domain ell E X.left n).lift ((domain ell E Y.left n).ι ⋙
    FiniteRestriction.conjugate (Ring ell E n) (encoding n)
      (sfFiniteExceptionalAt (ULift.{u + 1} (Ring ell E n)) c))
    (operations_preserve ell E D hell f c encoding n).2

/-- Exactly the etale-origin Hom normalization, including the coefficient-equivalence
unit, for every origin witness. Source: normalized restriction adjunction
(blueprint: def-sf-finite-exceptional-constructions). -/
def AdjunctionNormalized (n : ℕ)
    (a : F ell E D hell f c encoding n ⊣ G ell E D hell f c encoding n) : Prop :=
  ∀ (M : _root_.DerivedCategory.Plus
      (Sheaf (ProEt.topology X.left) (ModuleCat.{u + 1} (ULift.{u + 1} (Ring ell E n)))))
    (N : _root_.DerivedCategory.Plus
      (Sheaf (ProEt.topology Y.left) (ModuleCat.{u + 1} (ULift.{u + 1} (Ring ell E n)))))
    (hM : domain ell E X.left n ((encoding n X.left).fixedDerived.inverse.obj M.obj))
    (hN : domain ell E Y.left n ((encoding n Y.left).fixedDerived.inverse.obj N.obj))
    (W : FixedEtaleOriginWitness X.left (ULift.{u + 1} (Ring ell E n)) M)
    (v : (FiniteRestriction.fixedSupport (Ring ell E n) c).obj M.obj ⟶ N.obj),
    (a.homEquiv ⟨_, hM⟩ ⟨_, hN⟩
      (ObjectProperty.homMk
        ((FiniteRestriction.comparison (Ring ell E n) (encoding n) c).hom.app M.obj ≫
          (encoding n Y.left).fixedDerived.inverse.map v))).hom =
      (encoding n X.left).fixedDerived.inverse.map
        (specifiedExceptionalHomEquiv (ULift.{u + 1} (Ring ell E n)) c M W N v ≫
          (sfFiniteExceptionalAt (ULift.{u + 1} (Ring ell E n)) c).map
            ((encoding n Y.left).fixedDerived.counitIso.inv.app N.obj))

/-- The first retained unique-existence obligation. Source: paragraph 1
(blueprint: def-sf-finite-exceptional-constructions).
Proof: normalizedRestrictionAdjunction applies to these literal restrictions, with
identity restriction equalities. Its natural Hom bijections give the adjunction.
Every constructible input has an etale origin, so the normalization determines every
Hom bijection. Adjunction extensionality gives uniqueness, including unit and counit. -/
theorem adjunction_existsUnique (n : ℕ) :
    ∃! a : F ell E D hell f c encoding n ⊣ G ell E D hell f c encoding n,
      AdjunctionNormalized ell E D hell f c encoding n a := by
  sorry

/-- Choose only from the uniquely Hom-normalized adjunction. Source: paragraph 1
(blueprint: def-sf-finite-exceptional-constructions). -/
def adjunction (n : ℕ) : F ell E D hell f c encoding n ⊣ G ell E D hell f c encoding n :=
  (adjunction_existsUnique ell E D hell f c encoding n).choose

/-- The ordinary dual-pullback-dual functor, before restricting its source.
Source: paragraph 1 (blueprint: def-sf-finite-exceptional-constructions). -/
def H (n : ℕ) :=
  (dual ell E D hell Y n).rightOp ⋙
    (moduleObjectDerivedPullback (coefficient ell E n).X f.left).op ⋙
      dual ell E D hell X n

/-- The same object and arrow in the constant-model native presentation.
Source: finite-domain identification (blueprint: def-sf-finite-exceptional-constructions). -/
def asCtf (T : Over (Spec (.of D.k)))
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom] (n : ℕ)
    (K : (domain ell E T.left n).FullSubcategory) :
    ConstantModelConstructibleFiniteTor (coefficient ell E n).X T.left :=
  ⟨K.obj, (congrArg (fun P ↦ P K.obj) (domain_eq ell E D T n)).mp K.property⟩

/-- The specified compactification as a boundary object.
Source: compactification coherence (blueprint: def-sf-finite-exceptional-constructions). -/
def boundary : Compactification.BoundaryCompactification f.left := by
  letI : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  letI : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
  letI : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  exact ⟨⟨c, Compactification.quasiCompact_openImmersion _ inferInstance⟩⟩

set_option maxHeartbeats 800000 in
-- Comparing the two nested derived compactification functors exceeds the default 200000 budget.
/-- The second retained unique-existence obligation, with the concrete trace/evaluation
normalization. Source: paragraph 1 (blueprint: def-sf-finite-exceptional-constructions).
Proof: finite biduality and pullback preserve the domain. The four specified Hom
bijections are evaluation/biduality on Y, the absolute-trace Complement, the ordinary
pullback/direct-image adjunction, and symmetric evaluation on X. They give a right
adjoint with the displayed Hom action. Right-adjoint uniqueness identifies it with G;
the image of the counit is the displayed component. Hom injectivity forces uniqueness. -/
theorem dualFormula_existsUnique (n : ℕ) :
    ∃! t : G ell E D hell f c encoding n ⋙ (domain ell E X.left n).ι ≅
      (domain ell E Y.left n).ι ⋙ H ell E D hell f n,
      FormulaNormalized ell E D hell f c encoding n t := by
  sorry

/-- Select the unique trace/evaluation-normalized dual formula. Source: paragraph 1
(blueprint: def-sf-finite-exceptional-constructions). -/
def dualFormulaIso (n : ℕ) :
    G ell E D hell f c encoding n ⋙ (domain ell E X.left n).ι ≅
      (domain ell E Y.left n).ι ⋙ H ell E D hell f n :=
  (dualFormula_existsUnique ell E D hell f c encoding n).choose

/-- Invertibility of the specified compact-support map, without flatness of the quotient.
Source: lem-fix-compact-support-coefficient-change, paragraph 2
(blueprint: def-sf-finite-exceptional-constructions).
Proof: on bounded finite-Tor etale-origin representatives the open scalar map and the
proper direct-image coefficient comparison give the actual compact-support tensor map.
The finite coefficient equivalence preserves its unit/counit normalization. The cited
comparison is invertible, and the full inclusion reflects invertibility. -/
theorem qMap_isIso {m n : ℕ} (h : n ≤ m) : IsIso (qMap ell E D hell f c encoding h) := by
  sorry

/-- The restricted actual compact-support comparison, with its fixed orientation.
Source: q in paragraph 2 (blueprint: def-sf-finite-exceptional-constructions). -/
def q {m n : ℕ} (h : n ≤ m) :
    F ell E D hell f c encoding m ⋙ Q ell E Y.left h ≅
      Q ell E X.left h ⋙ F ell E D hell f c encoding n :=
  @asIso _ _ _ _ (qMap ell E D hell f c encoding h) (qMap_isIso ell E D hell f c encoding h)

/-- The prescribed mate of q inverse under the selected normalized adjunctions.
Source: b in paragraph 2 (blueprint: def-sf-finite-exceptional-constructions). -/
def b {m n : ℕ} (h : n ≤ m) :
    G ell E D hell f c encoding m ⋙ Q ell E X.left h ⟶
      Q ell E Y.left h ⋙ G ell E D hell f c encoding n :=
  (mateEquiv (adjunction ell E D hell f c encoding m) (adjunction ell E D hell f c encoding n)
    (TwoSquare.mk _ _ _ _ (q ell E D hell f c encoding h).inv)).natTrans

end WeilConjectures.NativeFiniteExceptional
