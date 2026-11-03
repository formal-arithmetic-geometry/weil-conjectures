/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
public import WeilConjectures.AlgebraicGeometry.CondensedRationalAdjunction.CondensedRationalAdjunction
public import WeilConjectures.AlgebraicGeometry.NativeRationalFieldTransport.NativeRationalFieldAdjunctionTransport
public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDescentTwoColimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportFamily
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportScalarLines
public import Mathlib.CategoryTheory.Adjunction.Unique

import WeilConjectures.Algebra.Homology.OrdinaryLineScalar.OrdinaryLineDerivedScalarComparison
import WeilConjectures.AlgebraicGeometry.Integral.IntegralModels
import WeilConjectures.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousCoefficientModuleEncodingSupplement
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
import WeilConjectures.AlgebraicGeometry.Locally.LocallyPerfectScalarModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedScalarCoefficientMaps
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.CategoryTheory.ObjectProperty.Shift
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixCtfGenerators
import Mathlib.CategoryTheory.Triangulated.Adjunction
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleOrigin
import WeilConjectures.AlgebraicGeometry.Flat.FlatModelGeneration
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleLisseModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleExtensionIso
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartLocallyClosedExtension
import Mathlib.CategoryTheory.Triangulated.Generators
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
import WeilConjectures.ConstructibleSheaf.OpenClosed
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartSheafConeWitness
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralDerivedCoefficientData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralConstantModelLocalResolution
import WeilConjectures.ProperBaseChange.IntegralLfpLocallyFreeResolution
import WeilConjectures.ProperBaseChange.CondensedConstructibleSerre
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocallyClosedGeneratorTensorIntersection
import WeilConjectures.AlgebraicGeometry.Integral.IntegralLfpConstantModelComparison
import WeilConjectures.AlgebraicGeometry.CondensedLocallyClosedExtensionTower
import WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement

import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
import WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixAdmissibleThickness
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.Defs.Filter
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicConstantLocalModelTor
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.AlgebraicGeometry.Sites.QuasiCompact
import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeMapDerivedCategory
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralLisseDerivedAux
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalLeftDerived
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
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
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
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

/-! # Condensed algebraic-closure purity adjunction

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-sp-qbar/
  sk-thm-sp-qbar-adjunction.md (blueprint: prop-pur-condensed-qbar-adjunction).

The rational adjunctions are universally supplied with their rationalization and
integral normalization; the conclusion retains their actual units and counits.
The Hom-colimit composite is specified on every finite representative and every
choice of model isomorphisms. Together with the recorded Hom-descent theorem, this
is its universal representative description, including independence of models.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.PurityTransport
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedQbarPurityAdjunction

/-- The finite-field inclusion as a bundled condensed ring map.
Source: coefficient transitions (blueprint: prop-pur-condensed-qbar-adjunction). -/
def fieldMap (ell : ℕ) [Fact ell.Prime]
    {E F : PadicAlgCl.FiniteIntermediateField ell} (h : E ≤ F) :
    (Coefficient.rational E).bundled.{u} ell ⟶ (Coefficient.rational F).bundled ell :=
  CommMon.homMk (Mon.Hom.mk (Profinite.padicSubfieldRingObjMap ell h))

/-- The inclusion into the finite-subextension-valued algebraic-closure sheaf.
Source: coefficient transitions (blueprint: prop-pur-condensed-qbar-adjunction). -/
def closureMap (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell) :
    (Coefficient.rational E).bundled.{u} ell ⟶ Coefficient.closure.bundled ell :=
  CommMon.homMk (Mon.Hom.mk (Profinite.padicSubfieldRingObjToPadicAlgCl ell E))

/-- Restriction of the actual derived scalar extension; only membership is supplied.
Source: scalar endpoints (blueprint: prop-pur-condensed-qbar-adjunction). -/
def extend (ell : ℕ) [Fact ell.Prime] {c c' : Coefficient ell}
    (a : c.bundled.{u} ell ⟶ c'.bundled ell) (T : Scheme.{u})
    (h : ∀ K, property ell c T K → property ell c' T ((scalarSixChange a T).obj K)) :
    c.ctf ell T ⥤ c'.ctf ell T :=
  (property ell c' T).lift ((property ell c T).ι ⋙ scalarSixChange a T)
    (fun K ↦ h K.obj K.property)

/-- The two native scalar endpoints, normalized by the actual compact-support mate
and the native pullback/Tate-line comparison.
Source: displayed Hom composite (blueprint: prop-pur-condensed-qbar-adjunction). -/
structure Comparisons (ell : ℕ) [Fact ell.Prime]
    (D : WeilConjectures.FiniteFieldDatum.{u}) (s : SmoothDatum D)
    {c c' : Coefficient ell} (a : c.bundled ell ⟶ c'.bundled ell)
    (A : ExplicitAdjunction ell D c s) (B : ExplicitAdjunction ell D c' s) where
  hX : ∀ K, property ell c s.X.left K → property ell c' s.X.left
    ((scalarSixChange a s.X.left).obj K)
  hY : ∀ K, property ell c s.Y.left K → property ell c' s.Y.left
    ((scalarSixChange a s.Y.left).obj K)
  coefficient_normalization : c.integralMap ell ≫ a.hom.hom = c'.integralMap ell
  line : ScalarLineCoordinates ell a coefficient_normalization s.X.left
  b : support ell c s.compactification A.support_closed ⋙ extend ell a s.Y.left hY ≅
    extend ell a s.X.left hX ⋙ support ell c' s.compactification B.support_closed
  j : source ell c s.map s.dim A.source_closed ⋙ extend ell a s.X.left hX ≅
    extend ell a s.Y.left hY ⋙ source ell c' s.map s.dim B.source_closed
  b_normalized : ∀ M : c.ctf ell s.X.left,
    (b.hom.app M).hom = (scalarSupportMap a s.compactification).app M.obj
  j_normalized : ∀ K : c.ctf ell s.Y.left,
    (j.hom.app K).hom =
      sourceScalar ell a s.map s.dim coefficient_normalization line K.obj

/-- The actual unit, counit, and Hom transition equations, retaining native maps.
Source: scalar-change equations (blueprint: prop-pur-condensed-qbar-adjunction). -/
structure TransitionLaws (ell : ℕ) [Fact ell.Prime]
    (D : WeilConjectures.FiniteFieldDatum.{u}) (s : SmoothDatum D)
    {c c' : Coefficient ell} (a : c.bundled ell ⟶ c'.bundled ell)
    (A : ExplicitAdjunction ell D c s) (B : ExplicitAdjunction ell D c' s)
    (q : Comparisons ell D s a A B) : Prop where
  unit : ∀ M : c.ctf ell s.X.left,
    B.adjunction.unit.app ((extend ell a s.X.left q.hX).obj M) =
      (extend ell a s.X.left q.hX).map (A.adjunction.unit.app M) ≫
        q.j.hom.app _ ≫ (source ell c' s.map s.dim B.source_closed).map (q.b.hom.app M)
  counit : ∀ K : c.ctf ell s.Y.left,
    q.b.hom.app _ ≫ (support ell c' s.compactification B.support_closed).map
        (q.j.hom.app K) ≫
      B.adjunction.counit.app ((extend ell a s.Y.left q.hY).obj K) =
        (extend ell a s.Y.left q.hY).map (A.adjunction.counit.app K)
  hom : ∀ (M : c.ctf ell s.X.left) (K : c.ctf ell s.Y.left)
    (z : (support ell c s.compactification A.support_closed).obj M ⟶ K),
    B.adjunction.homEquiv ((extend ell a s.X.left q.hX).obj M)
        ((extend ell a s.Y.left q.hY).obj K)
        (q.b.inv.app M ≫ (extend ell a s.Y.left q.hY).map z) =
      (extend ell a s.X.left q.hX).map (A.adjunction.homEquiv M K z) ≫ q.j.hom.app K

set_option maxHeartbeats 1600000 in
-- Native scalar functor endpoints contain large derived-category expressions.
/-- Ordinary derived tensor associativity, with its actual coefficient-composite equality.
Source: coefficient cocycles (blueprint: prop-pur-condensed-qbar-adjunction). -/
@[irreducible]
def tower (ell : ℕ) [Fact ell.Prime]
    {c₁ c₂ c₃ : Coefficient ell}
    (a₁₂ : c₁.bundled.{u} ell ⟶ c₂.bundled ell)
    (a₂₃ : c₂.bundled.{u} ell ⟶ c₃.bundled ell)
    (a₁₃ : c₁.bundled.{u} ell ⟶ c₃.bundled ell)
    (h : a₁₂ ≫ a₂₃ = a₁₃) (T : Scheme.{u}) :
    scalarSixChange a₁₂ T ⋙ scalarSixChange a₂₃ T ≅ scalarSixChange a₁₃ T :=
  scalarSixTower a₁₂ a₂₃ T ≪≫ eqToIso (congrArg (fun a ↦ scalarSixChange a T) h)

/-- The endpoint cocycles in the ambient derived categories. Full-subcategory
inclusions preserve and reflect these equations, and the associators are exactly
ordinary derived tensor transitivity, rather than additional isomorphism data.
Source: field-transition transitivity (blueprint: prop-pur-condensed-qbar-adjunction). -/
def Cocycle (ell : ℕ) [Fact ell.Prime]
    (D : WeilConjectures.FiniteFieldDatum.{u}) (s : SmoothDatum D)
    {c₁ c₂ c₃ : Coefficient ell}
    (a₁₂ : c₁.bundled ell ⟶ c₂.bundled ell)
    (a₂₃ : c₂.bundled ell ⟶ c₃.bundled ell)
    (a₁₃ : c₁.bundled ell ⟶ c₃.bundled ell)
    (A : ExplicitAdjunction ell D c₁ s) (B : ExplicitAdjunction ell D c₂ s)
    (C : ExplicitAdjunction ell D c₃ s)
    (q₁₂ : Comparisons ell D s a₁₂ A B)
    (q₂₃ : Comparisons ell D s a₂₃ B C)
    (q₁₃ : Comparisons ell D s a₁₃ A C) : Prop :=
  ∃ map_comp : a₁₂ ≫ a₂₃ = a₁₃,
    (∀ M : c₁.ctf ell s.X.left,
      (scalarSixChange a₂₃ s.Y.left).map (q₁₂.b.hom.app M).hom ≫
          (q₂₃.b.hom.app ((extend ell a₁₂ s.X.left q₁₂.hX).obj M)).hom ≫
          (CondensedRing.rightDerivedLowerShriekOfCompactification
            (c₃.obj ell) s.compactification).map
            ((tower ell a₁₂ a₂₃ a₁₃ map_comp s.X.left).hom.app M.obj) =
        (tower ell a₁₂ a₂₃ a₁₃ map_comp s.Y.left).hom.app
            ((support ell c₁ s.compactification A.support_closed).obj M).obj ≫
          (q₁₃.b.hom.app M).hom) ∧
    (∀ K : c₁.ctf ell s.Y.left,
      (scalarSixChange a₂₃ s.X.left).map (q₁₂.j.hom.app K).hom ≫
          (q₂₃.j.hom.app ((extend ell a₁₂ s.Y.left q₁₂.hY).obj K)).hom ≫
          (c₃.smoothSource ell s.map s.dim).map
            ((tower ell a₁₂ a₂₃ a₁₃ map_comp s.Y.left).hom.app K.obj) =
        (tower ell a₁₂ a₂₃ a₁₃ map_comp s.X.left).hom.app
            ((source ell c₁ s.map s.dim A.source_closed).obj K).obj ≫
          (q₁₃.j.hom.app K).hom)

/-- The model-independent representative formula for the Hom-colimit bijection.
It quantifies over every finite field and every chosen model identification.
Source: displayed Hom composite (blueprint: prop-pur-condensed-qbar-adjunction). -/
def ModelFormula (ell : ℕ) [Fact ell.Prime]
    (D : WeilConjectures.FiniteFieldDatum.{u}) (s : SmoothDatum D)
    (A : ∀ E : PadicAlgCl.FiniteIntermediateField ell,
      ExplicitAdjunction ell D (.rational E) s)
    (B : ExplicitAdjunction ell D (.closure) s)
    (q : ∀ E : PadicAlgCl.FiniteIntermediateField ell,
      Comparisons ell D s (closureMap ell E) (A E) B) : Prop :=
  ∀ (E : PadicAlgCl.FiniteIntermediateField ell)
    (M₀ : (Coefficient.rational E).ctf ell s.X.left)
    (K₀ : (Coefficient.rational E).ctf ell s.Y.left)
    (M : Coefficient.closure.ctf ell s.X.left)
    (K : Coefficient.closure.ctf ell s.Y.left)
    (i : (extend ell (closureMap ell E) s.X.left (q E).hX).obj M₀ ≅ M)
    (j : (extend ell (closureMap ell E) s.Y.left (q E).hY).obj K₀ ≅ K)
    (z : (support ell (.rational E) s.compactification (A E).support_closed).obj M₀ ⟶ K₀),
    B.adjunction.homEquiv M K
      ((support ell (.closure) s.compactification B.support_closed).map i.inv ≫
        (q E).b.inv.app M₀ ≫
        (extend ell (closureMap ell E) s.Y.left (q E).hY).map z ≫ j.hom) =
      i.inv ≫ (extend ell (closureMap ell E) s.X.left (q E).hX).map
        ((A E).adjunction.homEquiv M₀ K₀ z) ≫
        (q E).j.hom.app K₀ ≫ (source ell (.closure) s.map s.dim B.source_closed).map j.hom

set_option maxHeartbeats 1600000 in
-- Native scalar functor endpoints contain large derived-category expressions.
end AlgebraicGeometry.ProEtale.CondensedQbarPurityAdjunction
