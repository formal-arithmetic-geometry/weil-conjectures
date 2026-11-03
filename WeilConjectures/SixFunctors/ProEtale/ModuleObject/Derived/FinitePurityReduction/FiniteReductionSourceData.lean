/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FinitePurityReduction.FiniteReductionCoefficientData
public import WeilConjectures.AlgebraicGeometry.FiniteReductionRootCharts.FiniteReductionRootCharts
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
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntTensorProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdmissibleTensorConstructibility
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
public import WeilConjectures.Compactification.Over
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixFiniteGeneration
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixNonfiniteGeneration
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixAdmissibleThickness
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixPerfectExtension
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixCtfGenerators
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
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixCtf
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
public import Mathlib.AlgebraicGeometry.Noetherian
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
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonLocalizing
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Mathlib.CategoryTheory.Triangulated.Subcategory
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
public import WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement
public import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCycleClass
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportCompact
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixHomTensorShiftCancellation

/-! # Canonical finite-reduction pullback and root-chart normalization data

Source: finite-reduction proof Step 2, pullback, twists and canonical shifts.
(blueprint: def-pur-finite-reduction-source-data).
The chart conjugate and normalization predicate are actual definitions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing.FinitePurityReduction

variable (ell : ℕ) [Fact ell.Prime]
variable (E : Type u) [Field E] [Algebra (Padic ell) E]
  [FiniteDimensional (Padic ell) E]

/-- The exact restriction/pullback square's scalar-adjunction mate. It is defined
on every unbounded object, with no flatness, finite-Tor or finite-type restriction.
Source: finite-reduction Step 2 (blueprint: def-pur-finite-reduction-source-data). -/
def pullback (m n : ℕ) (hmn : m ≤ n) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    scalarSixPull (coefficient ell E n) f ⋙ scalarSixChange (quotient ell E m n hmn) X ⟶
      scalarSixChange (quotient ell E m n hmn) Y ⋙ scalarSixPull (coefficient ell E m) f :=
  scalarSixPullHom (quotient ell E m n hmn) f

/-- The isomorphism fixed by this mate. Source: nonflat pullback compatibility
(blueprint: def-pur-finite-reduction-source-data). -/
def pullbackIso (m n : ℕ) (hmn : m ≤ n) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    scalarSixPull (coefficient ell E n) f ⋙ scalarSixChange (quotient ell E m n hmn) X ≅
      scalarSixChange (quotient ell E m n hmn) Y ⋙ scalarSixPull (coefficient ell E m) f :=
  PurityTransport.scalarPullbackIso (quotient ell E m n hmn) f

/-- The specified shift of the pullback comparison, with scalar extension's
adjunction-induced shift structure. Source: Step 2, the untwisted root coordinates
(blueprint: def-pur-finite-reduction-source-data). -/
def shiftedPullback (m n : ℕ) (hmn : m ≤ n) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (d : ℕ) (K : DerivedCategory (ModuleRingedComparison.internalModules
      (coefficient ell E n).X Y)) :
    (scalarSixChange (quotient ell E m n hmn) X).obj
        (((scalarSixPull (coefficient ell E n) f).obj K) ⟦2 * (d : ℤ)⟧) ≅
      (((scalarSixPull (coefficient ell E m) f).obj
        ((scalarSixChange (quotient ell E m n hmn) Y).obj K)) ⟦2 * (d : ℤ)⟧) :=
  letI := scalarSixChangeCommShift (quotient ell E m n hmn) X
  ((scalarSixChange (quotient ell E m n hmn) X).commShiftIso
    (2 * (d : ℤ))).app _ ≪≫
      (shiftFunctor _ (2 * (d : ℤ))).mapIso ((pullbackIso ell E m n hmn f).app K)

/-- The prescribed comparison in a particular compatible pair of primitive-root
charts: reduce the first chart, apply the shifted pullback mate, and undo the
second chart. Source: Step 2
(blueprint: def-pur-finite-reduction-source-data). -/
def sourceInCharts (m n : ℕ) (hmn : m ≤ n) {k : Type u} [Field k]
    {X Y : Over (Spec (.of k))} (f : X ⟶ Y) (d : ℕ)
    (K : DerivedCategory (ModuleRingedComparison.internalModules
      (coefficient ell E n).X Y.left)) {ζ η : k}
    (hζ : IsPrimitiveRoot ζ (ell ^ (n + 1)))
    (hη : IsPrimitiveRoot η (ell ^ (m + 1))) :=
  (scalarSixChange (quotient ell E m n hmn) X.left).mapIso
    (FiniteReductionRootCharts.sourceChart ell E X.hom n hζ
      ((scalarSixPull (coefficient ell E n) f.left).obj K) d) ≪≫
    shiftedPullback ell E m n hmn f.left d K ≪≫
      (FiniteReductionRootCharts.sourceChart ell E X.hom m hη
        ((scalarSixPull (coefficient ell E m) f.left).obj
          ((scalarSixChange (quotient ell E m n hmn) Y.left).obj K)) d).symm

/-- Normalization in every compatible primitive-root chart. Source: Step 2
(blueprint: def-pur-finite-reduction-source-data). -/
def SourceNormalized (m n : ℕ) (hmn : m ≤ n) {k : Type u} [Field k]
    {X Y : Over (Spec (.of k))} (f : X ⟶ Y) (d : ℕ)
    (K : DerivedCategory (ModuleRingedComparison.internalModules
      (coefficient ell E n).X Y.left))
    (e : (scalarSixChange (quotient ell E m n hmn) X.left).obj
      (((coefficientFiniteTwistFunctor ell E X.left n (d : ℤ)).obj
        ((scalarSixPull (coefficient ell E n) f.left).obj K)) ⟦2 * (d : ℤ)⟧) ≅
      (((coefficientFiniteTwistFunctor ell E X.left m (d : ℤ)).obj
        ((scalarSixPull (coefficient ell E m) f.left).obj
          ((scalarSixChange (quotient ell E m n hmn) Y.left).obj K))) ⟦2 * (d : ℤ)⟧)) : Prop :=
  ∀ (ζ η : k) (hζ : IsPrimitiveRoot ζ (ell ^ (n + 1)))
    (hη : IsPrimitiveRoot η (ell ^ (m + 1))),
    η = ζ ^ (ell ^ (n - m)) → e = sourceInCharts ell E m n hmn f d K hζ hη

end AlgebraicGeometry.ProEtale.CondensedRing.FinitePurityReduction
