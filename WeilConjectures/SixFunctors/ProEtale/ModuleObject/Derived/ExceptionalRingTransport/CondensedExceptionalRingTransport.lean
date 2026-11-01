/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TensorHomExchangeCore
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
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportProjectionFormula
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
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
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsFlat
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.CategoryTheory.MorphismProperty.Retract
public import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ImmersionProjectionScalarNormalization
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import WeilConjectures.CategoryTheory.RingedDerivedComparisons.RingedDerivedMonoidalComparisons
import WeilConjectures.CategoryTheory.Scalar.ScalarInternalHomDataSupplement
import WeilConjectures.SmoothPurity.Coefficient.CoefficientSystemScalarCalculus
import WeilConjectures.CategoryTheory.SixFunctors.SignedDerivedInternalHomExact
import WeilConjectures.CategoryTheory.SixFunctors.EvaluationShiftTransport
import WeilConjectures.CategoryTheory.SixFunctors.ContravariantIsoLocus
import WeilConjectures.CategoryTheory.RingedSignedTensor.RingedTensorSignedCancellation
import WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
import Mathlib.Algebra.Homology.BifunctorShift
import WeilConjectures.SixFunctors.Coefficient.Tensor.CoefficientTensorCurryNormalization
import WeilConjectures.CategoryTheory.Scalar.ScalarHomComparisonTower
import WeilConjectures.Algebra.Homology.Derived.DerivedScalarExtensionCounitShift
import WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Retract
public import WeilConjectures.CategoryTheory.Monoidal.Closed.IhomComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OperationComparisons.CondensedOperationComparisons
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportComparisonDefinitions
public import Mathlib.CategoryTheory.Shift.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.AlgebraicGeometry.Native.NativeHomSourceShiftData
public import WeilConjectures.AlgebraicGeometry.Native.NativeDerivedHomSignedExact
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek

/-! # Exceptional tensor--Hom transport for ordinary condensed coefficients

Source: latest blueprint, `sk-thm-sf-tensor-hom`, its Complement and Yoneda proof
(blueprint: lem-sf-exceptional-ring-transport-core).

The comparison squares below use the published scalar tensorator, evaluation transpose,
proper/open compact-support comparison, direct-image mate, and exceptional counit mate.
In particular the coefficient compatibility is an equality of the specified arrows.

## Main definitions

* `verdierExchange` and `exceptionalDualExchange` are the specified duality comparisons.
* `ScalarSquare`, `ProperBidualSquare`, `ShiftSquares`, and `Natural` are morphism equations.
* `Stage`, `StageMap`, and `Data` package the explicit coefficient regimes and conclusions.

## Main statements

* `exists_condensed_exceptional_ring_transport` states the complete transport assertion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor MonoidalCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing.ExceptionalRingTransport

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  (hcd : BaseFieldFiniteCD ℓ k)
  (Λ : ScalarSixRing.{u}) (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ.X)
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

/-- Native shift of an object in the full Dctf subcategory, with membership from
constructible and finite-Tor thickness. Source: native-shift clause of the Complement
(blueprint: lem-sf-exceptional-ring-transport-core). -/
def shiftObject (T : Over (Spec (.of k))) [LocallyOfFiniteType T.hom]
    [QuasiCompact T.hom] [IsSeparated T.hom]
    (K : ConstantModelConstructibleFiniteTor Λ.X T.left) (n : ℤ) :
    ConstantModelConstructibleFiniteTor Λ.X T.left := by
  letI := (sfbAdmissibleConstructibleThickness ℓ Λ hΛ k T).1
  letI := (constantModelConstructibleFiniteTor_wellDefined Λ.X T.left).2.2.2.2.2.2.2.1
  exact ⟨K.obj⟦n⟧, ObjectProperty.le_shift _ n K.obj K.property⟩

/-- The native exceptional shift mate, uniquely fixed by the compact-support shift
and the exceptional counit. Source: native-shift clause of the Complement
(blueprint: lem-sf-exceptional-ring-transport-core). -/
def exceptionalShift (L : ConstantModelConstructibleFiniteTor Λ.X Y.left) (n : ℤ) :
    ((ctfExceptionalInverseImage Λ.X ℓ k hcd f hΛ).obj L).obj⟦n⟧ ⟶
      ((ctfExceptionalInverseImage Λ.X ℓ k hcd f hΛ).obj
        (shiftObject ℓ k Λ hΛ Y L n)).obj :=
  ((ctfExceptionalAdjunction Λ.X ℓ k hcd f hΛ).homEquiv
    (shiftObject ℓ k Λ hΛ X ((ctfExceptionalInverseImage Λ.X ℓ k hcd f hΛ).obj L) n)
    (shiftObject ℓ k Λ hΛ Y L n)
    (ObjectProperty.homMk
      (((rightDerivedLowerShriekOfCompactification Λ.X
          (compactificationOverField f)).commShiftIso n).hom.app
            ((ctfExceptionalInverseImage Λ.X ℓ k hcd f hΛ).obj L).obj ≫
        (((ctfExceptionalAdjunction Λ.X ℓ k hcd f hΛ).counit.app L).hom) ⟦n⟧'))).hom

/-- Exactly the four coefficient regimes of the statement. Finite quotients retain
an arbitrary uniformizer and a positive exponent. The closure is the fixed standard
algebraic closure of Q_ell, with its finite-subextension-valued condensed ring.
Source: finite-stage paragraph (blueprint: lem-sf-exceptional-ring-transport-core). -/
inductive Stage (ℓ : ℕ) [Fact ℓ.Prime] : Type
  | integral (E : PadicAlgCl.FiniteIntermediateField ℓ)
  | rational (E : PadicAlgCl.FiniteIntermediateField ℓ)
  | closed
  | finite (E : PadicAlgCl.FiniteIntermediateField ℓ) (π : PadicAlgCl.integers ℓ E.1)
      (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1))
      (n : ℕ+)

/-- The actual ordinary condensed coefficient ring at a stage, using the discrete
finite quotient and the finite-subextension-valued closure. The lift only places the
small finite ring in the common site universe.
Source: finite-stage paragraph (blueprint: lem-sf-exceptional-ring-transport-core). -/
def Stage.ring : Stage ℓ → ScalarSixRing.{u}
  | .integral E => ⟨Profinite.padicIntegersRingObj ℓ E.1⟩
  | .rational E => ⟨Profinite.continuousMapRingObj E.1⟩
  | .closed => ⟨Profinite.padicAlgClRingObj ℓ⟩
  | .finite E π _ n => ⟨cartesianFinitePointRing
      (ULift.{u} (PadicAlgCl.integers ℓ E.1 ⧸ (Ideal.span {π}) ^ (n : ℕ)))⟩

/-- The normalized integral quotient map, specified on every profinite section.
No flatness is imposed. Source: derived finite reductions in the Complement
(blueprint: lem-sf-exceptional-ring-transport-core). -/
def IsReduction (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1))
    (n : ℕ+) (a : Stage.ring.{u} ℓ (.integral E) ⟶ Stage.ring ℓ (.finite E π hπ n)) :
    Prop :=
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
  ∀ (P : Profinite.{u}) (s : ULift.{u + 1} C(P, PadicAlgCl.integers ℓ E.1)) (x : P),
    (((a.hom.hom.hom.app (op P)) s).down x).down =
      Ideal.Quotient.mk ((Ideal.span {π}) ^ (n : ℕ)) (s.down x)

/-- The normalized successive finite reduction, induced by the identity on O_E.
Source: successive reductions in the Complement
(blueprint: lem-sf-exceptional-ring-transport-core). -/
def IsSuccessiveReduction (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1))
    (n : ℕ+)
    (a : Stage.ring.{u} ℓ (.finite E π hπ (n + 1)) ⟶
      Stage.ring ℓ (.finite E π hπ n)) : Prop :=
  ∀ (P : Profinite.{u})
      (s : (Stage.ring.{u} ℓ (.finite E π hπ (n + 1))).X.obj.obj (op P)) (x : P),
    (((a.hom.hom.hom.app (op P)) s).down x).down =
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n : ℕ))))
        ((s.down x).down)

/-- Precisely the scalar maps in the finite-stage assertion, including their
successive composites. The quotient maps are characterized sectionwise, rather than
being arbitrary ring maps or chosen isomorphisms.
Source: finite-stage compatibility and successive changes
(blueprint: lem-sf-exceptional-ring-transport-core). -/
inductive StageMap : {s t : Stage ℓ} → (Stage.ring.{u} ℓ s ⟶ Stage.ring ℓ t) → Prop
  | localization (E : PadicAlgCl.FiniteIntermediateField ℓ)
      (a : Stage.ring.{u} ℓ (.integral E) ⟶ Stage.ring ℓ (.rational E))
      (ha : a.hom.hom = (sheafCompose (coherentTopology Profinite.{u})
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          (Profinite.padicIntegersCondensedRingToPadicSubfieldCondensedRing ℓ E.1)) :
      StageMap a
  | closure (E : PadicAlgCl.FiniteIntermediateField ℓ)
      (a : Stage.ring.{u} ℓ (.rational E) ⟶ Stage.ring ℓ .closed)
      (ha : a.hom.hom = Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) : StageMap a
  | integers (E F : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F)
      (a : Stage.ring.{u} ℓ (.integral E) ⟶ Stage.ring ℓ (.integral F))
      (ha : a.hom.hom = finiteCoefficientIntegersPointMap ℓ h) : StageMap a
  | fields (E F : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F)
      (a : Stage.ring.{u} ℓ (.rational E) ⟶ Stage.ring ℓ (.rational F))
      (ha : a.hom.hom = Profinite.padicSubfieldRingObjMap ℓ h) : StageMap a
  | reduction (E : PadicAlgCl.FiniteIntermediateField ℓ)
      (π : PadicAlgCl.integers ℓ E.1)
      (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1))
      (n : ℕ+)
      (a : Stage.ring.{u} ℓ (.integral E) ⟶ Stage.ring ℓ (.finite E π hπ n))
      (ha : IsReduction ℓ E π hπ n a) : StageMap a
  | successiveReduction (E : PadicAlgCl.FiniteIntermediateField ℓ)
      (π : PadicAlgCl.integers ℓ E.1)
      (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1))
      (n : ℕ+)
      (a : Stage.ring.{u} ℓ (.finite E π hπ (n + 1)) ⟶
        Stage.ring ℓ (.finite E π hπ n))
      (ha : IsSuccessiveReduction ℓ E π hπ n a) : StageMap a
  | comp {s t r : Stage ℓ}
      (a : Stage.ring.{u} ℓ s ⟶ Stage.ring ℓ t)
      (b : Stage.ring.{u} ℓ t ⟶ Stage.ring ℓ r)
      (ha : StageMap a) (hb : StageMap b) : StageMap (a ≫ b)

/-- Qbar exceptional tensor--Hom transport with its specified finite-stage scalar
compatibility, evaluation transposes, proper bidual square and native integer shifts.

Source: latest blueprint `sk-thm-sf-tensor-hom`, its Complement and proof
(blueprint: lem-sf-exceptional-ring-transport-core).

Proof plan:
1. Match the restricted exceptional adjunction of operations (vi) to the localizing
Brown adjunction by counit-compatible uniqueness (det-sp-unique-right-adjoint and
sk-thm-existence). For E, O_E and Qbar use lem-integral-ctf-equals-bc.
2. Specialize sk-thm-sf-tensor-hom to each of the explicit condensed stage rings.
Its Yoneda chain gives the canonical exchange map of the core. At the dualizing
object, conjugate the normalized compact-support compositor to obtain
 dualizingIdentification and hence verdierExchange. The same projection/evaluation
transpose gives exceptionalDualExchange. These constructions retain evaluation.
3. In the proper case identify compact support with direct image using the normalized
trivial compactification. Transpose its evaluation pairing twice to obtain exactly
ProperBidualSquare. No equality of separately chosen functors is assumed.
4. Use det-prop-scalar-six-ctf on each listed stage map, including nonflat integral
and successive finite reductions. The scalar-six Hom transpose, direct-image mate,
compact-support comparison and exceptional counit mate give ScalarSquare. Apply the
same statement to StageMap.comp for successive changes. Qbar object and morphism
descent (sk-thm-sfb-qlbar-two-colimit) and naturality compare finite presentations
on a common larger finite field and make the resulting Qbar exchange independent
of the chosen presentation.
5. The native signed tensor/Hom shifts (lem-sf-condensed-derived-tensor-shifts) and
counit-compatible uniqueness of adjoint shifts
(lem-weil-pbc-adjunction-shift-compatibility-unique) identify the transposed shifts
with ShiftSquares, including the contravariant first variable. -/
theorem exists_condensed_exceptional_ring_transport : Nonempty (Data ℓ k hcd f) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.ExceptionalRingTransport
