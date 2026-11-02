/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Internal.InternalSignedTateTwist
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportLinePull
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportAdjunctions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TraceCupMixed.CondensedMixedSupportCup
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TraceCupProper.CondensedProperComparison
public import WeilConjectures.AlgebraicGeometry.CondensedPoincare.CondensedPoincareSetting
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportUnits
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.CategoryTheory.GrothendieckDerivedBrownRightAdjoint
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
public import WeilConjectures.Compactification.BoundaryRefinement
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.ExactDerivedAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportComparisonUnit
public import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.IntrinsicCondensedCoefficientPoint
public import WeilConjectures.AlgebraicGeometry.PurityTransport.Transport
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
import WeilConjectures.CategoryTheory.AdjunctionSquareComposition
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
public import WeilConjectures.AlgebraicGeometry.Picard.Purity.Condensed.NativeCompactSupportWeilTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportCompositionData
public import WeilConjectures.AlgebraicGeometry.SepFinType
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompBaseChangeDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedFrobeniusComparisonCoherence
public import WeilConjectures.AlgebraicGeometry.PurityCoefficientChange.CondensedPurityCoefficientChange
public import WeilConjectures.SixFunctors.FiniteFieldDatum.FrobeniusSquareCartesian
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportPull
public import WeilConjectures.AlgebraicGeometry.RationalP1.Tate.RationalTateLineComposition
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsComapUnit
public import WeilConjectures.Compactification.CommonDenseRefinement

/-! # Trace and trace--cup pairing in pulled-back condensed coefficients

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-poincare-duality/sec-the-trace-map-in-top-degree/sk-cor-trace/
sk-def-trace-cup/_section.md, the untwisted counit and final pairing display;
its representative-level reading is def-pod-trace-cup-reading.md in that directory.
(blueprint: sk-def-trace-cup)
The orientation is the uniquely integration-normalized purity family. The derived
trace is inverse twist cancellation followed by its constructible smooth counit.
The ordinary trace and cup are transported by the canonical proper comparison.
The target retains the negative Tate line without choosing a basis.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonObj
open MonoidalCategory MonoidalClosed Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.CurrentTraceCup

open PurityTransport

variable (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell)

/-- The root-line specialization needed for K_- in this definition. Positive powers
are the existing purity root line; negative powers are its internal dual into the
coefficient unit. This is an item helper, not a replacement attachment for the
published general signed-twist node.
Source: K_- and its twist cancellation (blueprint: sk-def-trace-cup), using the
signed-power display of sk-def-sp-tate-twist. -/
def signedLine (T : Scheme.{u}) : ℤ →
    Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj (c.obj ell) T)
  | .ofNat n => c.line ell T n
  | .negSucc n => (ihom (c.line ell T (n + 1))).obj (𝟙_ _)

/-- The root-line representative of Lambda_T(r) in degree zero.
Source: K_- = Lambda_s(-d) (blueprint: sk-def-trace-cup). -/
def derivedLine (T : Scheme.{u}) (r : ℤ) : c.derived ell T :=
  (DerivedCategory.singleFunctor _ 0).obj (signedLine ell c T r)

/-- The Tate representative used by U_X is constructible and has finite Tor amplitude.
Source: K_- in the defining U_X display (blueprint: sk-def-trace-cup), and the
compatible-root-cover construction of sk-def-sp-tate-twist.
Proof: on a pro-etale cover choose compatible primitive roots at every ell-power
level. The integral inverse limit is then the coefficient unit, compatibly with all
level projections. Scalar extension gives the same identification for a finite
coefficient, O_E and E; the maps commute with finite-subextension transitions, so the
sheafified colimit gives it for Qbar. Tensor powers and internal duals are locally
rank-one free as well. Thus the degree-zero object is constructible and flat, and
its Tor amplitude is [0,0]. This includes degree zero and non-field finite rings. -/
theorem tateLine_mem (T : Scheme.{u})
    [∀ x : T, Invertible (ell : T.residueField x)] (r : ℤ) :
    property ell c T (derivedLine ell c T r) := by
  sorry

set_option maxHeartbeats 0 in
-- Native tensor and derived-functor comparisons elaborate large instance terms.
/-- Evaluation of the positive Tate line against its signed inverse; at zero it is
unit multiplication. Source: twist cancellation (blueprint: sk-def-trace-cup). -/
def evaluation (T : Scheme.{u}) : (d : ℕ) →
    c.line ell T d ⊗ signedLine ell c T (-(d : ℤ)) ⟶ 𝟙_ _
  | 0 => (λ_ _).hom
  | d + 1 => (ihom.ev (c.line ell T (d + 1))).app (𝟙_ _)

set_option maxHeartbeats 0 in
-- Native tensor and derived-functor comparisons elaborate large instance terms.
/-- The root-normalized pullback coordinates; the normalization fields determine every
map, including tensor power zero. Source: Cartesian twists
(blueprint: sk-def-trace-cup). -/
def linePull {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (ell : X.residueField x)]
    [∀ y : Y, Invertible (ell : Y.residueField y)] :=
  (linePullCoordinates_nonempty ell c f).some

set_option maxHeartbeats 0 in
-- Native tensor and derived-functor comparisons elaborate large instance terms.
/-- Twist pullback followed by evaluation, with the cohomological shift [2d].
This is the actual cancellation arrow, before proving it invertible.
Source: the source identification of U_X (blueprint: sk-def-trace-cup). -/
def cancellation {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (ell : X.residueField x)]
    [∀ y : Y, Invertible (ell : Y.residueField y)] (d : ℕ) :
    (c.smoothSource ell f d).obj (derivedLine ell c Y (-(d : ℤ))) ⟶
      (unit ell c X) ⟦2 * (d : ℤ)⟧ :=
  letI : BraidedCategory (c.derived ell X) := DerivedCategory.braidedCategory' _
  let F := upperStar (c.obj ell) f
  let N := signedLine ell c Y (-(d : ℤ))
  let e := (linePull ell c f).power d
  let v : c.line ell X d ⊗ F.obj N ⟶ 𝟙_ _ :=
    (e.inv ⊗ₘ 𝟙 _) ≫ Functor.LaxMonoidal.μ F _ _ ≫
      F.map (evaluation ell c Y d) ≫ (Functor.Monoidal.εIso F).inv
  (((tensorLeft _).commShiftIso (2 * (d : ℤ))).app _).hom ≫
    (shiftFunctor _ (2 * (d : ℤ))).map
      (((((F.singleFunctorCompLeftDerivedFunctorIso).app N).hom) ⊗ₘ 𝟙 _) ≫
        (β_ _ _).hom ≫
        (singleTensor ell c X _ _ (line_flat ell c X d)).hom ≫
        (DerivedCategory.singleFunctor _ 0).map v)

set_option synthInstance.maxHeartbeats 0 in
-- The large cancellation composite needs unrestricted instance search.
/-- Cancellation is invertible at every coefficient stage.
Source: the twist evaluation identification in the defining paragraph
(blueprint: sk-def-trace-cup).
Proof: on a compatible primitive-root cover the positive line is the coefficient
unit and its negative signed line is its internal dual. The displayed map becomes
unit multiplication, hence is invertible. Inverse image, the flat single-tensor
comparison and shift preserve these isomorphisms. Invertibility descends from the
pro-etale cover. The argument includes d=0 and finite non-field coefficient rings. -/
theorem cancellation_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (ell : X.residueField x)]
    [∀ y : Y, Invertible (ell : Y.residueField y)] (d : ℕ) :
    IsIso (cancellation ell c f d) := by
  sorry

set_option maxHeartbeats 0 in
-- Native tensor and derived-functor comparisons elaborate large instance terms.
/-- The signed coefficient Tate line as an actual constructible finite-Tor complex.
Source: K_- = Lambda_s(-d) (blueprint: sk-def-trace-cup). -/
def minus (Y : Scheme.{u}) [∀ y : Y, Invertible (ell : Y.residueField y)]
    (d : ℕ) : c.ctf ell Y :=
  ⟨derivedLine ell c Y (-(d : ℤ)),
    tateLine_mem ell c Y (-(d : ℤ))⟩

set_option maxHeartbeats 0 in
-- Native tensor and derived-functor comparisons elaborate large instance terms.
/-- Base change preserves the stated geometric property of X_0.
Source: geometric fibre in the fixed setting (blueprint: sk-def-trace-cup). -/
instance geometricProper (D : WeilConjectures.FiniteFieldDatum.{u}) (d : ℕ)
    (G : PoincareDualitySetting D.k₀ d) [IsProper G.modelStructureMorphism] :
    IsProper (G.structureMorphism D.k) :=
  inferInstanceAs (IsProper (pullback.snd G.modelStructureMorphism
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))

/-- Base change preserves the stated geometric property of X_0.
Source: geometric fibre in the fixed setting (blueprint: sk-def-trace-cup). -/
instance geometricSeparated (D : WeilConjectures.FiniteFieldDatum.{u}) (d : ℕ)
    (G : PoincareDualitySetting D.k₀ d) :
    IsSeparated (G.structureMorphism D.k) :=
  inferInstanceAs (IsSeparated (pullback.snd G.modelStructureMorphism
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))

/-- Base change preserves the stated geometric property of X_0.
Source: geometric fibre in the fixed setting (blueprint: sk-def-trace-cup). -/
instance geometricQuasiCompact (D : WeilConjectures.FiniteFieldDatum.{u}) (d : ℕ)
    (G : PoincareDualitySetting D.k₀ d) :
    QuasiCompact (G.structureMorphism D.k) :=
  inferInstanceAs (QuasiCompact (pullback.snd G.modelStructureMorphism
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))

/-- Base change preserves the stated geometric property of X_0.
Source: geometric fibre in the fixed setting (blueprint: sk-def-trace-cup). -/
instance geometricFiniteType (D : WeilConjectures.FiniteFieldDatum.{u}) (d : ℕ)
    (G : PoincareDualitySetting D.k₀ d) :
    LocallyOfFiniteType (G.structureMorphism D.k) :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd G.modelStructureMorphism
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))

/-- Base change preserves the stated geometric property of X_0.
Source: geometric fibre in the fixed setting (blueprint: sk-def-trace-cup). -/
instance geometricSmoothDimension (D : WeilConjectures.FiniteFieldDatum.{u}) (d : ℕ)
    (G : PoincareDualitySetting D.k₀ d) :
    SmoothOfRelativeDimension d (G.structureMorphism D.k) :=
  inferInstanceAs (SmoothOfRelativeDimension d (pullback.snd G.modelStructureMorphism
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))

set_option maxHeartbeats 0 in
-- Native tensor and derived-functor comparisons elaborate large instance terms.
/-- The geometric index of the actual base-changed smooth proper model, with identity
compactification. Source: X_0, X and a_X (blueprint: sk-def-trace-cup). -/
def geometry (D : WeilConjectures.FiniteFieldDatum.{u}) (d : ℕ)
    (G : PoincareDualitySetting D.k₀ d) [IsProper G.modelStructureMorphism] :
    SmoothDatum D :=
  { X := Over.mk (G.structureMorphism D.k)
    xFinite := geometricFiniteType D d G
    xQuasiCompact := geometricQuasiCompact D d G
    xSeparated := geometricSeparated D d G
    Y := Over.mk (𝟙 (Spec (.of D.k)))
    yFinite := inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of D.k))))
    yQuasiCompact := inferInstanceAs (QuasiCompact (𝟙 (Spec (.of D.k))))
    ySeparated := inferInstanceAs (IsSeparated (𝟙 (Spec (.of D.k))))
    map := G.structureMorphism D.k
    isOver := (Scheme.Hom.isOver_iff (Spec (.of D.k))).mpr (Category.comp_id _)
    separated := geometricSeparated D d G
    finiteType := geometricFiniteType D d G
    quasiCompact := geometricQuasiCompact D d G
    dim := d
    smooth := geometricSmoothDimension D d G
    compactification := Compactification.ofIsProper (G.structureMorphism D.k) }

set_option maxHeartbeats 0 in
-- Native tensor and derived-functor comparisons elaborate large instance terms.
/-- Construct the required residue inverses from ell different from the characteristic.
Source: distinct primes in the fixed setting (blueprint: sk-def-trace-cup). -/
@[instance_reducible]
def residueInverse (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (T : Over (Spec (.of D.k))) : ∀ x : T.left, Invertible (ell : T.left.residueField x) :=
  fun x ↦ (map_natCast (T.hom.residueFieldAlgebraMap x) ell) ▸
    ((primeUnit D ell hEll).map (T.hom.residueFieldAlgebraMap x)).invertible

/-- Cohomology classes represented by scalar-unit maps to the shifted coefficient complex.
Source: representatives Lambda[-i] -> RΓ, equivalently Lambda -> RΓ[i]
(blueprint: sk-def-trace-cup). -/
abbrev Classes (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (M : DerivedCategory (ModuleCat.{u + 1} (Γ Λ))) (i : ℤ) :=
  (𝟙_ (DerivedCategory (ModuleCat.{u + 1} (Γ Λ)))) ⟶ M⟦i⟧

set_option maxHeartbeats 0 in
-- Native tensor and derived-functor comparisons elaborate large instance terms.
/-- Tensor two class representatives, extract their shifts, then apply the given
coefficient-complex product. Source: the representative prescription
(blueprint: sk-def-trace-cup). -/
def product {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ]
    {M N P : DerivedCategory (ModuleCat.{u + 1} (Γ Λ))}
    (mulMap : M ⊗ N ⟶ P) (i j : ℤ) (x : Classes Λ M i) (y : Classes Λ N j) :
    Classes Λ P (i + j) :=
  (λ_ _).inv ≫ (x ⊗ₘ y) ≫
    (DerivedCategory.shiftTensorShiftIso _ M N i j).hom ≫ mulMap⟦i + j⟧'

set_option maxHeartbeats 0 in
-- Native tensor and derived-functor comparisons elaborate large instance terms.
/-- The canonical h_r induced by the proper comparison on coefficient complexes.
Source: kappa and h_r (blueprint: sk-def-trace-cup). -/
def properClassComparison (D : WeilConjectures.FiniteFieldDatum.{u}) (d : ℕ)
    (G : PoincareDualitySetting D.k₀ d) [IsProper G.modelStructureMorphism] (i : ℤ) :
    Classes (c.obj ell)
      ((condensedRingCompactCoefficientComplex (c.obj ell)
        (Compactification.ofIsProper (G.structureMorphism D.k))).obj
          (unit ell c (G.geometricFiber D.k))) i ≃
    Classes (c.obj ell)
      ((condensedRingOrdinaryCoefficientComplex (c.obj ell)
        (G.structureMorphism D.k)).obj (unit ell c (G.geometricFiber D.k))) i :=
  (Iso.refl _).homCongr
    ((shiftFunctor _ i).mapIso
      ((Functor.isoWhiskerRight (TraceCupProper.comparison (c.obj ell)
        (G.structureMorphism D.k))
          (TraceCupPoint.fiber (c.obj ell) D.k)).app _))

set_option maxHeartbeats 0 in
-- Native tensor and derived-functor comparisons elaborate large instance terms.
/-- Ordinary cup is h_(i+j) of the mixed-support product of h_i inverse x and y,
followed by compact-support coefficient-unit multiplication. Source: cup display
(blueprint: sk-def-trace-cup). -/
def cupRepresentatives (D : WeilConjectures.FiniteFieldDatum.{u}) (d : ℕ)
    (G : PoincareDualitySetting D.k₀ d) [IsProper G.modelStructureMorphism]
    (i j : ℤ)
    (x : Classes (c.obj ell) ((condensedRingOrdinaryCoefficientComplex (c.obj ell)
      (G.structureMorphism D.k)).obj (unit ell c (G.geometricFiber D.k))) i)
    (y : Classes (c.obj ell) ((condensedRingOrdinaryCoefficientComplex (c.obj ell)
      (G.structureMorphism D.k)).obj (unit ell c (G.geometricFiber D.k))) j) :=
  let a := G.structureMorphism D.k
  let C := Compactification.ofIsProper a
  let K := unit ell c (G.geometricFiber D.k)
  let m : K ⊗ K ⟶ K :=
    ((DerivedCategory.singleFunctorObjUnitIso _).hom ⊗ₘ 𝟙 K) ≫ (λ_ K).hom
  properClassComparison ell c D d G (i + j)
    (product
      (TraceCupMixed.cup (c.bundled ell) D.k C K K ≫
        (condensedRingCompactCoefficientComplex (c.obj ell) C).map m) i j
      ((properClassComparison ell c D d G i).symm x) y)

set_option maxHeartbeats 0 in
-- Native tensor and derived-functor comparisons elaborate large instance terms.
set_option maxHeartbeats 0 in
-- Native tensor and derived-functor comparisons elaborate large instance terms.
/-- Canonical identification of scalar-unit representatives with actual cohomology.
It first uses the projective scalar module and then evaluates a linear map at 1.
Source: the representative prescription (blueprint: sk-def-trace-cup). -/
def classEquiv {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ]
    (M : DerivedCategory (ModuleCat.{u + 1} (Γ Λ))) (i : ℤ) :
    Classes Λ M i ≃ ↥((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (Γ Λ)) i).obj M) :=
  ((DerivedCategory.singleFunctorObjUnitIso _).symm.homCongr (Iso.refl _)).trans
    (((DerivedCategory.shiftFunctorCompPreadditiveCoyonedaObjSingleFunctorZeroIso
      (ModuleCat.of (Γ Λ) (Γ Λ)) i).app M).addCommGroupIsoToAddEquiv.toEquiv.trans
        ((ModuleCat.homLinearEquiv (R := Γ Λ) (S := ℤ)
          (M := ModuleCat.of (Γ Λ) (Γ Λ))
          (N := (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (Γ Λ)) i).obj M)).toEquiv.trans
          (LinearMap.ringLmapEquivSelf (Γ Λ) ℤ
            ↥((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (Γ Λ)) i).obj M)).toEquiv))

/-- Actual ordinary cohomology with constant coefficients in degree i.
Source: H^i(X,Lambda) (blueprint: sk-def-trace-cup). -/
abbrev H (D : WeilConjectures.FiniteFieldDatum.{u}) (d : ℕ)
    (G : PoincareDualitySetting D.k₀ d) (i : ℤ) :=
  (condensedRingOrdinaryCohomology (c.obj ell) (G.structureMorphism D.k) i).obj
    (unit ell c (G.geometricFiber D.k))

set_option maxHeartbeats 0 in
-- Native tensor and derived-functor comparisons elaborate large instance terms.
/-- The cup on actual ordinary cohomology groups, through their canonical representatives.
Source: h_(i+j) H_c(m) mu_c(h_i inverse x,y) (blueprint: sk-def-trace-cup). -/
def cup (D : WeilConjectures.FiniteFieldDatum.{u}) (d : ℕ)
    (G : PoincareDualitySetting D.k₀ d) [IsProper G.modelStructureMorphism]
    (i j : ℤ) (x : H ell c D d G i) (y : H ell c D d G j) : H ell c D d G (i + j) :=
  let M := (condensedRingOrdinaryCoefficientComplex (c.obj ell)
    (G.structureMorphism D.k)).obj (unit ell c (G.geometricFiber D.k))
  classEquiv (Λ := c.obj ell) M (i + j) (cupRepresentatives ell c D d G i j
    ((classEquiv (Λ := c.obj ell) M i).symm x)
    ((classEquiv (Λ := c.obj ell) M j).symm y))

/-- The coefficient Tate line, defined as exactly H^0 Fib_s(Lambda_s(-d)).
Source: the displayed definition of Lambda(-d) (blueprint: sk-def-trace-cup). -/
abbrev TateLineValue (D : WeilConjectures.FiniteFieldDatum.{u}) (d : ℕ) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (Γ (c.obj ell))) 0).obj
    ((TraceCupPoint.fiber (c.obj ell) D.k).obj
      (derivedLine ell c (Spec (.of D.k)) (-(d : ℤ))))

set_option maxHeartbeats 0 in
-- Native tensor and derived-functor comparisons elaborate large instance terms.
/-- The compact trace on actual cohomology, through the canonical projective-single
identification of representatives. Source: tau_X display (blueprint: sk-def-trace-cup). -/
def compactTrace (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (d : ℕ) (G : PoincareDualitySetting D.k₀ d) [IsProper G.modelStructureMorphism]
    (x : (condensedRingCompactCohomology (c.obj ell)
      (Compactification.ofIsProper (G.structureMorphism D.k)) (2 * (d : ℤ))).obj
        (unit ell c (G.geometricFiber D.k))) : TateLineValue ell c D d :=
  let M := (condensedRingCompactCoefficientComplex (c.obj ell)
    (Compactification.ofIsProper (G.structureMorphism D.k))).obj
      (unit ell c (G.geometricFiber D.k))
  let N := (TraceCupPoint.fiber (c.obj ell) D.k).obj
    (derivedLine ell c (Spec (.of D.k)) (-(d : ℤ)))
  let t := compactTraceRepresentatives ell c D hEll d G
    ((classEquiv (Λ := c.obj ell) M (2 * (d : ℤ))).symm x)
  classEquiv (Λ := c.obj ell) N 0 (t ≫ (shiftFunctorZero _ ℤ).inv.app N)

set_option maxHeartbeats 0 in
-- Native tensor and derived-functor comparisons elaborate large instance terms.
/-- The ordinary trace is exactly tau_X after the inverse cohomology proper comparison.
Source: tr_X^(-d) display (blueprint: sk-def-trace-cup). -/
def trace (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (d : ℕ) (G : PoincareDualitySetting D.k₀ d) [IsProper G.modelStructureMorphism]
    (x : H ell c D d G (2 * (d : ℤ))) : TateLineValue ell c D d :=
  compactTrace ell c D hEll d G
    (((TraceCupProper.cohomology (c.obj ell) (G.structureMorphism D.k)
      (2 * (d : ℤ))).inv.app (unit ell c (G.geometricFiber D.k))) x)

set_option maxHeartbeats 0 in
-- Native tensor and derived-functor comparisons elaborate large instance terms.
/-- The trace--cup pairing on actual homology modules for every integer i. The output
is exactly H^0 Fib_s(Lambda_s(-d)), without choosing a trivialization of its Tate line.
Source: latest blueprint sk-def-trace-cup, final display (blueprint: sk-def-trace-cup). -/
def pairing (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (d : ℕ) (G : PoincareDualitySetting D.k₀ d) [IsProper G.modelStructureMorphism]
    (i : ℤ) (x : H ell c D d G i) (y : H ell c D d G (2 * (d : ℤ) - i)) :
    TateLineValue ell c D d :=
  trace ell c D hEll d G
    ((eqToHom (congrArg (H ell c D d G)
      ((add_sub_assoc i (2 * (d : ℤ)) i).symm.trans
        (add_sub_cancel_left i (2 * (d : ℤ))))))
          (cup ell c D d G i (2 * (d : ℤ) - i) x y))

set_option maxHeartbeats 0 in
-- Native tensor and derived-functor comparisons elaborate large instance terms.
/-- The trace--cup pairing in precisely the four coefficient stages of the fixed setting.
All finite-field, coefficient, uniformizer, geometric and properness hypotheses are
explicit; the coefficient Tate line is H^0 Fib_s(Lambda_s(-d)).
Source: latest blueprint sk-def-trace-cup, entire definition (blueprint: sk-def-trace-cup). -/
def traceCupPairing (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell) (π : PadicAlgCl.integers ell E)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ell E))
    (n : ℕ) (hn : 1 ≤ n) (b : CondensedPoincare.Stage)
    (d : ℕ) (G : PoincareDualitySetting D.k₀ d) [IsProper G.modelStructureMorphism]
    (i : ℤ) :
    H ell (CondensedPoincare.coefficient ell E π hπ n hn b) D d G i →
      H ell (CondensedPoincare.coefficient ell E π hπ n hn b) D d G (2 * (d : ℤ) - i) →
        TateLineValue ell (CondensedPoincare.coefficient ell E π hπ n hn b) D d :=
  pairing ell (CondensedPoincare.coefficient ell E π hπ n hn b) D hEll d G i

end AlgebraicGeometry.ProEtale.CondensedRing.CurrentTraceCup
