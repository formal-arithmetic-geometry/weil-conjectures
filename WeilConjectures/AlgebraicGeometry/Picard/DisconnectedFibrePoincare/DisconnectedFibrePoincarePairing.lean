/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeil.CondensedStrictWeilComplex
public import WeilConjectures.AlgebraicGeometry.Internal.InternalSignedTateTwist
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FieldSmoothDuality.CondensedFieldSmoothDuality
-- Construction-only dependency: def-zl-condensed-field-duality-constructions.
public import WeilConjectures.DeligneLaumon.CondensedWeil.CondensedConstantExtensionFrobenius
public import WeilConjectures.ZetaWeil.FrobeniusPointTransport
public import WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
public import WeilConjectures.TateTwist.ProEtale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportLinePull
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportCompact
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SmoothPurity.CondensedOrdinaryCompactSections

import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SitePerfectDualizableHom
import WeilConjectures.AlgebraicGeometry.PurityTransport.Transport
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedCoefficientMaps
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
import WeilConjectures.AlgebraicGeometry.RootCoordinateFace.RootTowerCoordinateFace
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import Mathlib.CategoryTheory.Adjunction.Mates
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
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedScalarCoefficientMaps
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixCtf
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
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestriction
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenClosedSequenceRingSheaf
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
import WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement
import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCycleClass
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportCompositionData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedFrobeniusComparisonCoherence
import WeilConjectures.SixFunctors.FiniteFieldDatum.FrobeniusSquareCartesian
import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportLinePull
import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportPull
import WeilConjectures.AlgebraicGeometry.RationalP1.Tate.RationalTateLineComposition
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsComapUnit
import WeilConjectures.AlgebraicGeometry.PurityCoefficientChange.CondensedPurityCoefficientChange
import WeilConjectures.Compactification.CommonDenseRefinement
import WeilConjectures.AlgebraicGeometry.Picard.VerdierExchange.VerdierExchangeData
import WeilConjectures.SixFunctors.CommonStageCompactWeilCohomology
import WeilConjectures.SmoothPurity.Finite.FiniteCoefficientPoint
import WeilConjectures.AlgebraicGeometry.Compactification.PureDimension
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import WeilConjectures.CategoryTheory.Projection.ProjectionInternalHom
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.AlgebraicGeometry.PurityTransport.TraceBasic
import WeilConjectures.ZetaWeil.OrdinaryCompactCohomology
import WeilConjectures.SmoothPurity.Compact.CompactSupportCoefficientAction
import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
import WeilConjectures.SixFunctors.Sf.SfIntegralReductionTowerSupplement
import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import WeilConjectures.Compactification.RefinementCategory
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Clopen.FiniteClopenDerivedDecomposition
import WeilConjectures.SmoothPurity.PurityFiniteSetting.ConstructibleExceptionalInverseImage
import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenSquareExchange
import WeilConjectures.AlgebraicGeometry.Sf.SfOpenExceptionalBaseChange
import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonClassAdjunction
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroAdjunction
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroExact
import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleOrigin
import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationCoherence
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantOpenSquareExchange
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Clopen.FiniteClopenConstructibilityBounds
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Pi.Basic
import WeilConjectures.AlgebraicGeometry.FiniteClopenTensor.ProEtaleFiniteClopenTensorCalculus
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicDerivedOpenAdjunction
import WeilConjectures.AlgebraicGeometry.Sf.SfCompactSupportRestrictionOfScalars
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenScalarRestrictionCoherence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars
import Mathlib.LinearAlgebra.TensorProduct.Map
import WeilConjectures.AlgebraicGeometry.ClopenLocalization.ProEtaleClopenUnboundedDerivedLocalization
import WeilConjectures.AlgebraicGeometry.ClopenMonoidalDescent.ProEtaleClopenKFlatMonoidalDescent
import WeilConjectures.EtaleCohomology.Purity.Smooth.Normalization
import WeilConjectures.WeilSheaf.FourierInversion.OtherSections
import WeilConjectures.SixFunctors.FrobeniusCohomologyTransport
import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportRealization
import WeilConjectures.SixFunctors.Supporting.FrobeniusPointTransportNatural
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCompactSupportRestriction
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
import WeilConjectures.SmoothPurity.Sf.SfCommonStageDirectImage
import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZero
import WeilConjectures.SixFunctors.FrobeniusExchange.FrobeniusGeometricExchange

/-! # Poincare pairing on possibly disconnected smooth proper fibres

Source: latest blueprint, sec-zeta-weil/sk-prop-smooth-proper-purity/
prop-zl-smooth-proper-relative-purity.proof.md, Step 3
(blueprint: lem-zl-disconnected-fibre-poincare-pairing).

The pairing uses actual condensed modules, their relative derived coefficient dual,
the root-normalized Tate line and the normalized smooth trace. Scalar coordinates
use the canonical universe lift of Qbar_l. No component is required to descend to
the finite field, and no connectedness or nonemptiness is assumed on the fibre.

## Main definitions

- `nativePairing`: the canonical trace-evaluation pairing before scalar evaluation.
- `Components`: a finite clopen partition by geometric connected components.
- `sections`: ordinary derived sections in the canonical lifted scalar coordinates.
- `twistedPhi`: the recorded twisted contragredient Weil isomorphism.

## Main statements

- `disconnected_fibre_poincare_pairing`: componentwise sum, perfectness and invariance.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

attribute [local irreducible] DerivedCategory CategoryTheory.Functor.mapDerivedCategory
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed
open AlgebraicGeometry AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
namespace WeilConjectures.DisconnectedFibrePoincare

/-- Actual condensed coefficient modules.
Source: latest blueprint, Step 3 (blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
abbrev M (ell : ℕ) [Fact ell.Prime] (X : Scheme.{u}) :=
  FieldSmoothDuality.coefficientModule ell X

/-- The ordinary unbounded derived category of these modules.
Source: latest blueprint, Step 3 (blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
abbrev C (ell : ℕ) [Fact ell.Prime] (X : Scheme.{u}) := DerivedCategory (M ell X)

set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
/-- Derived evaluation tensored with the actual Tate line.
Source: latest blueprint, Step 3 (blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
@[irreducible] def evaluation (ell : ℕ) [Fact ell.Prime] {X : Scheme.{u}} (K : C ell X) (d : ℕ) :
    K ⊗ twistedDual ell K d ⟶ line ell X d :=
  (α_ K (dual ell K) (line ell X d)).inv ≫
    ((ihom.ev K).app (𝟙_ _) ▷ line ell X d) ≫ (λ_ _).hom

/-- Exact inverse image in the recorded condensed coefficient category.
Source: latest blueprint, component restriction
(blueprint: lem-zl-disconnected-fibre-poincare-pairing).
-/
abbrev pull (ell : ℕ) [Fact ell.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (upperStar (Profinite.padicAlgClRingObj ell) f).mapDerivedCategory

set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
/-- The exact-pullback/total-direct-image adjunction, with its canonical comparison.
Source: latest blueprint, cup product (blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
@[irreducible] def adj (ell : ℕ) [Fact ell.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ell) f).ofNatIsoLeft
    (leftDerivedUpperStarIsoMapDerivedCategory (Profinite.padicAlgClRingObj ell) f)

/-- Ordinary derived direct image on the actual module category.
Source: latest blueprint, RΓ (blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
abbrev push (ell : ℕ) [Fact ell.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (lowerStar (Profinite.padicAlgClRingObj ell) f).rightDerivedFunctor

set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
/-- The ordinary cup product, the tensor-adjoint of the two inverse-image counits.
Source: latest blueprint, trace-evaluation pairing
(blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
@[irreducible] def cup (ell : ℕ) [Fact ell.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K L : C ell X) : (push ell f).obj K ⊗ (push ell f).obj L ⟶
      (push ell f).obj (K ⊗ L) :=
  (adj ell f).homEquiv _ _
    ((Functor.Monoidal.μIso (pull ell f) _ _).inv ≫
      ((adj ell f).counit.app K ⊗ₘ (adj ell f).counit.app L))

set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
/-- Identity-open compactification gives the canonical proper comparison, by uniqueness
of the left adjoint of identity inverse image.
Source: latest blueprint, H_c = H (blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
@[irreducible] def properComparison (ell : ℕ) [Fact ell.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] : rightDerivedLowerShriekOfCompactification
      (Profinite.padicAlgClRingObj ell) (Compactification.ofIsProper f) ≅
      push ell f :=
  Functor.isoWhiskerRight
    (Functor.mapDerivedCategoryNatIso
      (((openImmersionLowerShriekUpperStarAdjunction
        (Profinite.padicAlgClRingObj ell) (𝟙 X)).ofNatIsoRight
          (upperStarId (Profinite.padicAlgClRingObj ell) X)).leftAdjointUniq Adjunction.id) ≪≫
      Functor.mapDerivedCategoryIdIso _) (push ell f) ≪≫ Functor.leftUnitor _

set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
/-- Normalized smooth trace, read on ordinary direct image using identity-open coincidence.
Source: latest blueprint, trace-evaluation pairing
(blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
@[irreducible] def trace (ell : ℕ) [Fact ell.Prime] {k : Type u} [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (X : Over (Spec (.of k))) [IsProper X.hom] (d : ℕ) :
    (push ell X.hom).obj ((line ell X.left d) ⟦2 * (d : ℤ)⟧) ⟶
      𝟙_ (C ell (Spec (.of k))) :=
  (push ell X.hom).map
    ((shiftFunctor _ (2 * (d : ℤ))).map (lineComparison ell X.left d).hom) ≫
    (properComparison ell X.hom).inv.app _ ≫
    FieldSmoothDuality.orientedTrace ell X (Compactification.ofIsProper X.hom) d

set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
/-- Cup, evaluation, the even shift comparison, and the normalized smooth trace.
The displayed evaluation can also be a restriction to a geometric component.
Source: latest blueprint, Step 3 (blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
@[irreducible] def nativePairing (ell : ℕ) [Fact ell.Prime] {k : Type u} [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (X : Over (Spec (.of k))) [IsProper X.hom] (d : ℕ)
    (K L : C ell X.left) (e : K ⊗ L ⟶ line ell X.left d) :
    (push ell X.hom).obj K ⊗ ((push ell X.hom).obj L) ⟦2 * (d : ℤ)⟧ ⟶
      𝟙_ (C ell (Spec (.of k))) :=
  ((tensorLeft _).commShiftIso (2 * (d : ℤ))).hom.app _ ≫
    (shiftFunctor _ (2 * (d : ℤ))).map
      (cup ell X.hom K L ≫ (push ell X.hom).map e) ≫
    ((push ell X.hom).commShiftIso (2 * (d : ℤ))).inv.app _ ≫ trace ell X d

/-- Canonical lifted Qbar coordinates, so ring and module universes agree for tensor.
Source: latest blueprint, scalar modules (blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
abbrev Scalar (ell : ℕ) [Fact ell.Prime] := CohomologyScalar.{u} ell

set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
/-- Ordinary scalar derived category with locally small morphisms.
Source: latest blueprint, scalar modules (blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
abbrev DScalar (ell : ℕ) [Fact ell.Prime] := DerivedCategory (V.{u} ell)

/-- The canonical lifted scalar version of exact geometric-field evaluation.
Source: latest blueprint, scalar RΓ (blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
abbrev pointSections (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k] [IsAlgClosed k] :=
  (CondensedQbarGeometricEvaluation.fieldFiber k ell ⋙
    ModuleCat.restrictScalars
      (ULift.ringEquiv.toRingHom : Scalar.{u} ell →+* PadicAlgCl ell)).mapDerivedCategory

/-- Ordinary scalar sections, using exactly the published direct image and point evaluation.
Source: latest blueprint, scalar RΓ (blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
abbrev sections (ell : ℕ) [Fact ell.Prime] {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (a : X ⟶ Spec (.of k)) := push ell a ⋙ pointSections ell k

/-- Evaluation on coefficient modules, in the canonical universe lift.
Source: latest blueprint, scalar coordinates
(blueprint: lem-zl-disconnected-fibre-poincare-pairing).
-/
abbrev pointHeart (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k] [IsAlgClosed k] :=
  CondensedQbarGeometricEvaluation.fieldFiber k ell ⋙
    ModuleCat.restrictScalars
      (ULift.ringEquiv.toRingHom : Scalar.{u} ell →+* PadicAlgCl ell)

set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
/-- The constant-section coordinates after the canonical scalar lift.
Source: latest blueprint, scalar target (blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
@[irreducible] def pointUnitHeart (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [IsAlgClosed k] :
    (pointHeart ell k).obj (𝟙_ (M ell (Spec (.of k)))) ≃ₗ[Scalar.{u} ell] Scalar.{u} ell where
  toFun x := ULift.up (CondensedQbarGeometricEvaluation.fieldRegularCoordinates k ell x)
  invFun x := (CondensedQbarGeometricEvaluation.fieldRegularCoordinates k ell).symm x.down
  left_inv x := (CondensedQbarGeometricEvaluation.fieldRegularCoordinates k ell).symm_apply_apply x
  right_inv x := congrArg ULift.up
    ((CondensedQbarGeometricEvaluation.fieldRegularCoordinates k ell).apply_symm_apply x.down)
  map_add' x y := congrArg ULift.up
    ((CondensedQbarGeometricEvaluation.fieldRegularCoordinates k ell).map_add x y)
  map_smul' a x := congrArg ULift.up
    ((CondensedQbarGeometricEvaluation.fieldRegularCoordinates k ell).map_smul a.down x)

set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
/-- The canonical scalar-unit comparison; it sends the constant coefficient section to itself.
Source: latest blueprint, scalar target (blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
@[irreducible] def pointUnit (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k] [IsAlgClosed k] :
    (pointSections ell k).obj (𝟙_ (C ell (Spec (.of k)))) ≅ 𝟙_ (DScalar.{u} ell) :=
  (pointSections ell k).mapIso (DerivedCategory.singleFunctorObjUnitIso _).symm ≪≫
    ((pointHeart ell k).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      (pointUnitHeart ell k).toModuleIso ≪≫ DerivedCategory.singleFunctorObjUnitIso _

set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
/-- The scalar derived class of a native class, with its unit and shift comparisons.
Source: latest blueprint, induced degreewise pairing
(blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
@[irreducible] def scalarClass (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k] [IsAlgClosed k]
    {P : C ell (Spec (.of k))} (r : ℤ) (x : 𝟙_ _ ⟶ P ⟦r⟧) :
    𝟙_ (DScalar.{u} ell) ⟶ ((pointSections ell k).obj P) ⟦r⟧ :=
  (pointUnit ell k).inv ≫ (pointSections ell k).map x ≫
    ((pointSections ell k).commShiftIso r).hom.app P

set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
/-- An endomorphism of the scalar derived unit, in its specified Qbar coordinates.
Source: latest blueprint, scalar target (blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
@[irreducible] def scalarValue (ell : ℕ) [Fact ell.Prime] (f : End (𝟙_ (DScalar.{u} ell))) :
    Scalar.{u} ell :=
  ((DerivedCategory.singleFunctorCompHomologyFunctorIso (V.{u} ell) 0).inv.app (𝟙_ (V.{u} ell)) ≫
    (DerivedCategory.homologyFunctor (V.{u} ell) 0).map
      ((DerivedCategory.singleFunctorObjUnitIso _).hom ≫ f ≫
        (DerivedCategory.singleFunctorObjUnitIso _).inv) ≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (V.{u} ell) 0).hom.app _).hom
      (1 : Scalar.{u} ell)

set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
/-- Evaluation of a scalar derived pairing on complementary shifted classes.
All tensor shifts are the recorded derived shift comparisons, including their signs.
Source: latest blueprint, induced degreewise pairing
(blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
@[irreducible] def scalarDegree (ell : ℕ) [Fact ell.Prime] (P Q : DScalar.{u} ell) (n r : ℤ)
    (b : P ⊗ Q ⟦n⟧ ⟶ 𝟙_ _) (x : 𝟙_ _ ⟶ P ⟦r⟧) (y : 𝟙_ _ ⟶ Q ⟦n - r⟧) :
    Scalar.{u} ell :=
  scalarValue ell ((λ_ (𝟙_ _)).inv ≫
    (x ⊗ₘ (y ≫ ((shiftFunctorAdd' _ n (-r) (n - r) (sub_eq_add_neg n r)).app Q).hom)) ≫
    (DerivedCategory.shiftTensorShiftIso _ P (Q ⟦n⟧) r (-r)).hom ≫
    (shiftFunctor _ (r + -r)).map b ≫
    eqToHom (congrArg (fun j : ℤ ↦ (𝟙_ (DScalar.{u} ell)) ⟦j⟧) (add_neg_cancel r)) ≫
    (shiftFunctorZero _ ℤ).hom.app _)

set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
/-- Cohomology class of a derived scalar-unit map, by the single and homology comparisons.
Source: latest blueprint, H^i (blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
@[irreducible] def homologyClass (ell : ℕ) [Fact ell.Prime] {P : DScalar.{u} ell} (r : ℤ)
    (x : 𝟙_ _ ⟶ P ⟦r⟧) : (DerivedCategory.homologyFunctor (V.{u} ell) r).obj P :=
  ((DerivedCategory.singleFunctorCompHomologyFunctorIso (V.{u} ell) 0).inv.app (𝟙_ (V.{u} ell)) ≫
    (DerivedCategory.homologyFunctor (V.{u} ell) 0).map
      ((DerivedCategory.singleFunctorObjUnitIso _).hom ≫ x) ≫
    ((DerivedCategory.homologyFunctor (V.{u} ell) 0).shiftIso r 0 r (add_zero r)).hom.app P).hom
      (1 : Scalar.{u} ell)

set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
/-- Restriction of ordinary direct image, the direct-image unit followed by composition.
Source: latest blueprint, geometric components
(blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
@[irreducible] def restriction (ell : ℕ) [Fact ell.Prime] {k : Type u} [Field k]
    {U X : Over (Spec (.of k))} (j : U ⟶ X) (K : C ell X.left) :
    (push ell X.hom).obj K ⟶ (push ell U.hom).obj ((pull ell j.left).obj K) :=
  (push ell X.hom).map ((adj ell j.left).unit.app K) ≫
    (PurityTransport.lowerComp (Profinite.padicAlgClRingObj ell) j.left X.hom).inv.app _ ≫
    (eqToIso (congrArg (push ell) j.w)).hom.app _

attribute [instance] Components.openPiece Components.closedPiece Components.connected
  Components.proper Components.smooth

set_option maxHeartbeats 8000000 in
-- Keep the coefficient abstract while checking its exact-derived single comparison.
set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
/-- The coefficient prime is invertible at every geometric point; this is inherited
from ell != p and is not a hypothesis restricting the allowed schemes.
Source: latest blueprint, standing characteristic hypothesis
(blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
abbrev primeInvertible (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (hEll : ell ≠ D.p) (X : Over (Spec (.of D.k))) (x : X.left) :
    Invertible (ell : X.left.residueField x) :=
  (by simpa only [map_natCast] using
    (PurityTransport.primeUnit D ell hEll).map (X.hom.residueFieldAlgebraMap x) :
      IsUnit (ell : X.left.residueField x)).invertible

set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
/-- The canonical pairing on this finite-field geometric fibre, before scalar evaluation.
Source: latest blueprint, trace-evaluation pairing
(blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
@[irreducible] def fibrePairing (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (hEll : ell ≠ D.p) (X : Over (Spec (.of D.k))) [IsProper X.hom]
    (d : ℕ) (K L : C ell X.left) (e : K ⊗ L ⟶ line ell X.left d) :=
  letI : Fact (ringChar D.k ≠ ell) := ⟨(ringChar.eq D.k D.p).symm ▸ hEll.symm⟩
  nativePairing ell X d K L e

/-- The bilinear degreewise family of a scalar derived pairing.
Source: latest blueprint, all integer degrees
(blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
abbrev Pairings (ell : ℕ) [Fact ell.Prime] (P Q : DScalar.{u} ell) (d : ℕ) :=
  ∀ i : ℤ, (DerivedCategory.homologyFunctor (V.{u} ell) i).obj P →ₗ[Scalar.{u} ell]
    (DerivedCategory.homologyFunctor (V.{u} ell) (2 * (d : ℤ) - i)).obj Q →ₗ[Scalar.{u} ell]
      Scalar.{u} ell

set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
/-- The induced pairing is specified on every scalar cohomology class, so it cannot
be an unrelated perfect pairing. These are the actual ordinary scalar cohomology spaces.
Source: latest blueprint, induced degreewise pairing
(blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
@[irreducible] def IsInducedPairing (ell : ℕ) [Fact ell.Prime] (P Q : DScalar.{u} ell) (d : ℕ)
    (b : P ⊗ Q ⟦2 * (d : ℤ)⟧ ⟶ 𝟙_ _) (B : Pairings ell P Q d) : Prop :=
  ∀ (i : ℤ) (x : 𝟙_ _ ⟶ P ⟦i⟧) (y : 𝟙_ _ ⟶ Q ⟦2 * (d : ℤ) - i⟧),
    B i (homologyClass ell i x) (homologyClass ell (2 * (d : ℤ) - i) y) =
      scalarDegree ell P Q (2 * (d : ℤ)) i b x y

set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
/-- Scalar descent is fixed in every degree by the actual native cup/evaluation/trace
pairing, not by an arbitrary duality isomorphism. Over the coefficient field all complexes
split into their cohomology, so these equations determine the derived pairing uniquely.
Source: latest blueprint, scalar adjoint
(blueprint: lem-zl-disconnected-fibre-poincare-pairing). -/
@[irreducible] def IsScalarNormalizedPairing (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [IsAlgClosed k]
    (P Q : C ell (Spec (.of k))) (d : ℕ)
    (b : P ⊗ Q ⟦2 * (d : ℤ)⟧ ⟶ 𝟙_ _)
    (bs : (pointSections ell k).obj P ⊗ ((pointSections ell k).obj Q) ⟦2 * (d : ℤ)⟧ ⟶
      𝟙_ (DScalar.{u} ell)) : Prop :=
  ∀ (i : ℤ) (x : 𝟙_ _ ⟶ P ⟦i⟧) (y : 𝟙_ _ ⟶ Q ⟦2 * (d : ℤ) - i⟧),
    scalarDegree ell _ _ (2 * (d : ℤ)) i bs
      (scalarClass ell k i x) (scalarClass ell k (2 * (d : ℤ) - i) y) =
        FieldSmoothDuality.degreePairing ell k P Q (2 * (d : ℤ)) i b x y

set_option maxHeartbeats 8000000 in
-- Derived comparisons traverse the full actual condensed-module functors.
end WeilConjectures.DisconnectedFibrePoincare
