/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.SmoothTrace
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.PurityCompositionCoherence
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalOriginCompactSupportComposition
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionComparisons
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
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
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
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TraceBasicDefs
public import WeilConjectures.AlgebraicGeometry.Internal.InternalSignedTateTwist
public import Mathlib.CategoryTheory.Adjunction.Unique
public import WeilConjectures.AlgebraicGeometry.PurityTransport.FieldCompositionScalarData
public import WeilConjectures.AlgebraicGeometry.PurityTransport.FieldCompositionSourceGeometry
public import WeilConjectures.AlgebraicGeometry.PurityTransport.FieldCompositionSourceLines
public import WeilConjectures.AlgebraicGeometry.PurityTransport.FieldCompositionSourceWord
public import WeilConjectures.AlgebraicGeometry.Exact.ExactCondensedExchangeComparison
public import WeilConjectures.Compactification.Dense
public import WeilConjectures.AlgebraicGeometry.CondensedRationalAdjunction.CondensedRationalAdjunction
public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDescentTwoColimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralFlat
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteSmoothPullbackExchange
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteUniversalSmoothTrace
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Projection.ProjectionPurityCoordinates
public import WeilConjectures.AlgebraicGeometry.CoordinateSectionCoordinates.CoordinateSectionTateCoordinates
public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.AffineSpaceZeroSectionPurityStatement
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekIndependence

/-! # Trace normalization and transitivity

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-trace/sec-the-trace-map/sk-prop-sp-trace-composition/
thm-pur-trace-normalization-transitivity.md and its proof
(blueprint: thm-pur-trace-normalization-transitivity).

The finite coefficient ring is `Λ = A = A_{E,n} = P.Ring` of a `PurityFiniteSetting`
(def-pur-conventions). Its smooth traces are `PurityFiniteSetting.coefficientValuedSmoothTrace`
(def-pur-smooth-trace), the composition law `α_{g,f}` is `originCompositionAmbient`
(thm-sf-comp-composition), written in the intrinsic coordinates of the smooth trace by
`traceOriginCompositionInv` below, and the pullback-composition and twist-additivity
identification is `compositionSourceIdentification` (thm-pur-composition-coherence).
The finite reductions `A_{E,n} → A_{E,m}` are those of thm-pur-finite-reduction-of-purity.
The traces `t = ε Rf_!(γ)` for the condensed coefficients (det-sp-trace-basic,
sk-def-sp-trace) are the counits of the normalized family `normalizedFamily`; their
coefficient index runs over every coefficient presentation, the finite rings `A_{E,n}`
and `O_E` (`integral E`), `E` (`rational E`), `Q̄_ℓ` (`closure`) among them.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale.PurityTransport

namespace WeilConjectures.PurityFiniteSetting

/-- The inverse of the compact-support composition law `α_{g,f}` of thm-sf-comp-composition,
at an object `M` whose fixed-scalar presentation has an etale-origin witness `hM`, written in
the intrinsic coordinates in which `smoothCompactSupport` and the smooth trace are formed.
It is `α⁻¹` (the inverse of `originCompositionAmbient`) conjugated by the canonical intrinsic
compact-support comparisons of `f`, `g`, `gf` and the counit of the intrinsic realization.
Source: the arrow `α_{g,f}⁻¹` of the displayed composite
(blueprint: thm-pur-trace-normalization-transitivity). -/
def traceOriginCompositionInv (P : PurityFiniteSetting.{u}) {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (M : Scheme.proEtaleDerivedCategory X P.Ring)
    (hM : ProEtale.DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} P.Coefficient) X
      ((Scheme.sfIntrinsicDerivedEquivalence X P.Ring).inverse.obj M)) :
    (smoothCompactSupport P (f ≫ g)).obj M ⟶
      (smoothCompactSupport P g).obj ((smoothCompactSupport P f).obj M) := by
  letI : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  letI : Finite P.Coefficient := inferInstanceAs (Finite (ULift.{u + 1} P.Ring))
  letI hf := hasCompactification_of_finiteType_over_field P.field.k X Y f
  letI hg := hasCompactification_of_finiteType_over_field P.field.k Y Z g
  letI hfg := hasCompactification_of_finiteType_over_field P.field.k X Z (f ≫ g)
  let EX := Scheme.sfIntrinsicDerivedEquivalence X P.Ring
  let M' := EX.inverse.obj M
  let cf := HasCompactification.compactification f
  let cg := HasCompactification.compactification g
  let cfg := HasCompactification.compactification (f ≫ g)
  exact (smoothCompactSupport P (f ≫ g)).map (EX.counitIso.inv.app M) ≫
    (ProEtale.sfIntrinsicCompactSupportComparison P.Ring cfg).hom.app M' ≫
    (Scheme.sfIntrinsicDerivedEquivalence Z P.Ring).functor.map
      ((ProEtale.originCompositionAmbient P.Coefficient f g).inv.app ⟨M', hM⟩) ≫
    (ProEtale.sfIntrinsicCompactSupportComparison P.Ring cg).inv.app
      ((ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) f).obj M') ≫
    (smoothCompactSupport P g).map
      ((ProEtale.sfIntrinsicCompactSupportComparison P.Ring cf).inv.app M') ≫
    (smoothCompactSupport P g).map
      ((smoothCompactSupport P f).map (EX.counitIso.hom.app M))

/-- The finite compact-support base-change exchange `B : v^* Rf_! M → Rf'_! u^* M` for a
pullback square `u, f', f, v`, written in the intrinsic coordinates of `smoothCompactSupport`
(the chosen compactifications of `f` and `f'`). It is the canonical compactification support
exchange `sfFixedCompactSupportExchange` (proper direct-image base-change mate followed by the
extension-by-zero mate, for the base-changed compactification `c.ofIsPullback sq`), followed
by the canonical change of compactification from `c.ofIsPullback sq` to the chosen
compactification of `f'` on the etale-origin object `u^* M`
(`rightDerivedLowerShriekOfCompactificationOriginIso`, the etale independence of the
compactification transported along the compact-support comparisons), conjugated by the
intrinsic compact-support comparisons and the realization units/counits.
Source: "compatible with arbitrary base change of Z", the compact-support base change of
thm-cbc-finite-level-proetale with the comparison of compactifications
(blueprint: thm-pur-trace-normalization-transitivity). -/
def finiteCompactSupportBaseChange (P : PurityFiniteSetting.{u}) {X X' Y Y' : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [X'.Over (Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))] [Y'.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X' ↘ Spec (.of P.field.k))]
    [QuasiCompact (X' ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y' ↘ Spec (.of P.field.k))]
    (u : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (v : Y' ⟶ Y)
    [f.IsOver (Spec (.of P.field.k))] [f'.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
    (sq : IsPullback u f' f v) (M : Scheme.proEtaleDerivedCategory X P.Ring)
    (hM : ProEtale.DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} P.Coefficient) X'
      ((ProEtale.sfFixedDerivedPullback P.Ring u).obj
        ((Scheme.sfIntrinsicDerivedEquivalence X P.Ring).inverse.obj M))) :
    (P.finiteReductionPullback v).obj ((smoothCompactSupport P f).obj M) ⟶
      (smoothCompactSupport P f').obj ((P.finiteReductionPullback u).obj M) := by
  letI : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  letI : Finite P.Coefficient := inferInstanceAs (Finite (ULift.{u + 1} P.Ring))
  letI hf := hasCompactification_of_finiteType_over_field P.field.k X Y f
  letI hf' := hasCompactification_of_finiteType_over_field P.field.k X' Y' f'
  let EX := Scheme.sfIntrinsicDerivedEquivalence X P.Ring
  let EY := Scheme.sfIntrinsicDerivedEquivalence Y P.Ring
  let EY' := Scheme.sfIntrinsicDerivedEquivalence Y' P.Ring
  let M' := EX.inverse.obj M
  let N := (ProEtale.sfFixedDerivedPullback P.Ring u).obj M'
  let cf := HasCompactification.compactification f
  let cb := cf.ofIsPullback sq
  let cf' := HasCompactification.compactification f'
  let L : _root_.DerivedCategory.Plus _ := ⟨hM.choose, hM.choose_spec.1⟩
  let a := hM.choose_spec.2.some
  let change : (ProEtale.sfFixedCompactSupport P.Ring cb).obj N ⟶
      (ProEtale.sfFixedCompactSupport P.Ring cf').obj N :=
    (ProEtale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} P.Coefficient) cb).map a.inv ≫
      (ProEtale.rightDerivedLowerShriekOfCompactificationOriginIso P.Coefficient cb cf').hom.app
        L ≫
      (ProEtale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} P.Coefficient) cf').map a.hom
  exact (P.finiteReductionPullback v).map
      ((smoothCompactSupport P f).map (EX.counitIso.inv.app M) ≫
        (ProEtale.sfIntrinsicCompactSupportComparison P.Ring cf).hom.app M') ≫
    EY'.functor.map ((ProEtale.sfFixedDerivedPullback P.Ring v).map
      (EY.unitIso.inv.app ((ProEtale.sfFixedCompactSupport P.Ring cf).obj M'))) ≫
    EY'.functor.map ((ProEtale.sfFixedCompactSupportExchange P.Ring sq cf).app M') ≫
    EY'.functor.map change ≫
    (ProEtale.sfIntrinsicCompactSupportComparison P.Ring cf').inv.app N

/-- The compactly supported class `Λ_k → RΓ_c(A^d, Λ(d)[2d])` of a zero-section class `σ`
on `p_d : A^d → Spec k`, written in the source coordinates of the finite unit smooth trace
`smoothTrace` (def-pur-smooth-trace) for `Q = setting P n`, i.e. at `A_{E,n+1}`.
For `σ : z_* Λ → Λ(d)[2d]` on `A^d` (the ordered supported product of the coordinate
Cartier classes `ProEtale.AffineZeroPurity.supportedClass`, or of the Kummer classes
`ProEtale.AffineZeroPurity.kummerSupportedClass`), it is
`Λ ≅ R(id)_!Λ = R(p z)_!Λ ≅ Rp_! Rz_! Λ ≅ Rp_! z_*Λ → Rp_! Λ(d)[2d]`
(canonical identity and composition comparisons of thm-sf-comp-composition, the closed
single comparison, then `σ`), followed by the canonical identification of the target with
the diagonal twist (`orderedTargetComparison`), the intrinsic compact-support comparison and
the canonical identification `traceSourceIso` of the trace source with `Λ(d)[2d]`; the
initial arrow is the canonical unit comparison.
Source: "sends the ordered tensor ... of the Cartier classes of the coordinate zero
sections" (blueprint: thm-pur-trace-normalization-transitivity). -/
def finiteZeroSectionClass (P : PurityFiniteSetting.{u}) (n d : ℕ)
    [(Spec (.of (ProEtale.AffineZeroPurity.setting P n).field.k)).Over
      (Spec (.of (ProEtale.AffineZeroPurity.setting P n).field.k))]
    [(iteratedAffineLine (Spec (.of (ProEtale.AffineZeroPurity.setting P n).field.k)) d).Over
      (Spec (.of (ProEtale.AffineZeroPurity.setting P n).field.k))]
    [LocallyOfFiniteType (Spec (.of (ProEtale.AffineZeroPurity.setting P n).field.k) ↘
      Spec (.of (ProEtale.AffineZeroPurity.setting P n).field.k))]
    [QuasiCompact (Spec (.of (ProEtale.AffineZeroPurity.setting P n).field.k) ↘
      Spec (.of (ProEtale.AffineZeroPurity.setting P n).field.k))]
    [LocallyOfFiniteType
      (iteratedAffineLine (Spec (.of (ProEtale.AffineZeroPurity.setting P n).field.k)) d ↘
        Spec (.of (ProEtale.AffineZeroPurity.setting P n).field.k))]
    [QuasiCompact
      (iteratedAffineLine (Spec (.of (ProEtale.AffineZeroPurity.setting P n).field.k)) d ↘
        Spec (.of (ProEtale.AffineZeroPurity.setting P n).field.k))]
    [(iteratedAffineLineProj (Spec (.of (ProEtale.AffineZeroPurity.setting P n).field.k)) d).IsOver
      (Spec (.of (ProEtale.AffineZeroPurity.setting P n).field.k))]
    (σ : (ProEtale.cupSingle (ProEtale.AffineZeroPurity.setting P n)
        (iteratedAffineLine (Spec (.of (ProEtale.AffineZeroPurity.setting P n).field.k)) d)).obj
          ((ProEtale.lowerStar
            (ModuleCat.{u + 1} (ProEtale.AffineZeroPurity.setting P n).Coefficient)
            (ProEtale.AffineZeroPurity.zero
              (Spec (.of (ProEtale.AffineZeroPurity.setting P n).field.k)) d)).obj
              ((ProEtale.AffineZeroPurity.setting P n).constant
                (Spec (.of (ProEtale.AffineZeroPurity.setting P n).field.k)))) ⟶
      ProEtale.AffineZeroPurity.target P n
        (iteratedAffineLine (Spec (.of (ProEtale.AffineZeroPurity.setting P n).field.k)) d) d) :
    coefficientUnit (ProEtale.AffineZeroPurity.setting P n)
        (Spec (.of (ProEtale.AffineZeroPurity.setting P n).field.k)) ⟶
      (smoothCompactSupport (ProEtale.AffineZeroPurity.setting P n)
        (iteratedAffineLineProj (Spec (.of (ProEtale.AffineZeroPurity.setting P n).field.k)) d)).obj
          (traceSource (ProEtale.AffineZeroPurity.setting P n)
            (iteratedAffineLineProj
              (Spec (.of (ProEtale.AffineZeroPurity.setting P n).field.k)) d) d) := by
  let Q := ProEtale.AffineZeroPurity.setting P n
  let B := Spec (.of Q.field.k)
  let X := iteratedAffineLine B d
  let p := iteratedAffineLineProj B d
  let z := ProEtale.AffineZeroPurity.zero B d
  letI : Finite Q.Ring := Padic.finite_coefficientExtensionRing
    Q.coefficients.l Q.extension Q.level Q.level_pos
  letI : Finite Q.Coefficient := inferInstanceAs (Finite (ULift.{u + 1} Q.Ring))
  letI := ProEtale.AffineZeroPurity.zero_exact P n B (𝟙 _) d
  letI hp := hasCompactification_of_finiteType_over_field Q.field.k X B p
  letI hzp : HasCompactification (z ≫ p) :=
    HasCompactification.of_eq (f := 𝟙 B) (ProEtale.AffineZeroPurity.zero_proj B d).symm
  let EB := Scheme.sfIntrinsicDerivedEquivalence B Q.Ring
  let ho := ProEtale.AffineZeroPurity.unit_origin P n B
  let φ : ProEtale.AffineZeroPurity.unit P n B ⟶
      (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} Q.Coefficient) p).obj
        (ProEtale.AffineZeroPurity.target P n X d) :=
    ((ProEtale.originCompactSupportId Q.Coefficient B).inv.app
        ⟨ProEtale.AffineZeroPurity.unit P n B, ho⟩).hom ≫
      ((ProEtale.originCompactSupportCongr (A := Q.Coefficient) (f := 𝟙 B) (f' := z ≫ p)
        (ProEtale.AffineZeroPurity.zero_proj B d).symm).hom.app
          ⟨ProEtale.AffineZeroPurity.unit P n B, ho⟩).hom ≫
      (ProEtale.originCompositionAmbient Q.Coefficient z p).inv.app
        ⟨ProEtale.AffineZeroPurity.unit P n B, ho⟩ ≫
      (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} Q.Coefficient) p).map
        ((ProEtale.AffineZeroPurity.closedSingleIso Q.Coefficient z (Q.constant B)).hom ≫ σ)
  exact EB.functor.map (ProEtale.CoordinateSectionCoordinates.unitComparison P n B).hom ≫
    EB.functor.map φ ≫
    EB.functor.map ((ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} Q.Coefficient) p).map
      (ProEtale.CoordinateSectionCoordinates.orderedTargetComparison P n X
        (ProEtale.AffineSpacePurity.towerBase (𝟙 B) d) d).inv) ≫
    (ProEtale.sfIntrinsicCompactSupportComparison Q.Ring
      (HasCompactification.compactification p)).inv.app (Q.diagonalTwist X d) ≫
    (smoothCompactSupport Q p).map (traceSourceIso Q p d).inv

/-- The value of the finite unit smooth trace `Tr^sm_{p_d}` (def-pur-smooth-trace,
`smoothTrace`) of `Q = setting P n` (coefficients `A_{E,n+1}`) on the compactly supported
class `finiteZeroSectionClass` of a zero-section class `σ`, on `p_d : A^d → Spec k` over
the geometric point `Spec k`, with its canonical structure maps over `Spec k`.
Source: the displayed `Tr^sm_{p_d,Λ} : RΓ_c(A^d, Λ(d)[2d]) → Λ`
(blueprint: thm-pur-trace-normalization-transitivity). -/
def finiteAffineTraceValue (P : PurityFiniteSetting.{u}) (n d : ℕ)
    (σ : (ProEtale.cupSingle (ProEtale.AffineZeroPurity.setting P n)
        (iteratedAffineLine (Spec (.of (ProEtale.AffineZeroPurity.setting P n).field.k)) d)).obj
          ((ProEtale.lowerStar
            (ModuleCat.{u + 1} (ProEtale.AffineZeroPurity.setting P n).Coefficient)
            (ProEtale.AffineZeroPurity.zero
              (Spec (.of (ProEtale.AffineZeroPurity.setting P n).field.k)) d)).obj
              ((ProEtale.AffineZeroPurity.setting P n).constant
                (Spec (.of (ProEtale.AffineZeroPurity.setting P n).field.k)))) ⟶
      ProEtale.AffineZeroPurity.target P n
        (iteratedAffineLine (Spec (.of (ProEtale.AffineZeroPurity.setting P n).field.k)) d) d) :
    coefficientUnit (ProEtale.AffineZeroPurity.setting P n)
        (Spec (.of (ProEtale.AffineZeroPurity.setting P n).field.k)) ⟶
      coefficientUnit (ProEtale.AffineZeroPurity.setting P n)
        (Spec (.of (ProEtale.AffineZeroPurity.setting P n).field.k)) := by
  let Q := ProEtale.AffineZeroPurity.setting P n
  let B := Spec (.of Q.field.k)
  let X := iteratedAffineLine B d
  let p := iteratedAffineLineProj B d
  letI : B.Over B := ⟨𝟙 B⟩
  letI : X.Over B := ⟨p ≫ 𝟙 B⟩
  letI : LocallyOfFiniteType (B ↘ B) := inferInstanceAs (LocallyOfFiniteType (𝟙 B))
  letI : QuasiCompact (B ↘ B) := inferInstanceAs (QuasiCompact (𝟙 B))
  letI : LocallyOfFiniteType (X ↘ B) := inferInstanceAs (LocallyOfFiniteType (p ≫ 𝟙 B))
  letI : QuasiCompact (X ↘ B) := inferInstanceAs (QuasiCompact (p ≫ 𝟙 B))
  letI : p.IsOver B := ⟨rfl⟩
  letI : SmoothOfRelativeDimension d p := projection_smooth B d
  exact finiteZeroSectionClass P n d σ ≫ Q.smoothTrace p d

end WeilConjectures.PurityFiniteSetting

namespace WeilConjectures.SmoothTraceNormalization

/-- The geometric point `Spec k → Spec k` (k is algebraically closed in the conventions), as
an object over `Spec k`; the fibre of `p_d : A^d → Spec k` over it is `p_d` itself.
Source: "on every geometric fiber of p_d : A^d → Spec k"
(blueprint: thm-pur-trace-normalization-transitivity). -/
abbrev traceGeometricPoint (D : FiniteFieldDatum.{u}) : Over (Spec (.of D.k)) :=
  Over.mk (𝟙 (Spec (.of D.k)))

instance traceGeometricPoint_locallyOfFiniteType (D : FiniteFieldDatum.{u}) :
    LocallyOfFiniteType (traceGeometricPoint D).hom :=
  inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of D.k))))

instance traceGeometricPoint_quasiCompact (D : FiniteFieldDatum.{u}) :
    QuasiCompact (traceGeometricPoint D).hom :=
  inferInstanceAs (QuasiCompact (𝟙 (Spec (.of D.k))))

instance traceGeometricPoint_isSeparated (D : FiniteFieldDatum.{u}) :
    IsSeparated (traceGeometricPoint D).hom :=
  inferInstanceAs (IsSeparated (𝟙 (Spec (.of D.k))))

/-- Clause (1) of thm-pur-trace-normalization-transitivity: transitivity of the finite
smooth traces `Tr_{gf,K} = Tr_{g,K} ∘ Rg_!(Tr_{f,N}) ∘ α_{g,f}⁻¹` after the pullback-composition
and twist-additivity identification, with `N ∈ D^b_ctf(Y, A)` and the etale-origin witness.
Source: clause (1) (blueprint: thm-pur-trace-normalization-transitivity). -/
def TransitivityClause (P : PurityFiniteSetting.{u})
    {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [IsSeparated (Y ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    [IsSeparated (Z ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (d e : ℕ) [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g] : Prop :=
    ∀ (K : Scheme.proEtaleDerivedCategory Z P.Ring)
        (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Z K),
      ∃ (hN : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y
          ((P.compositionShiftedPullback g e).obj K))
        (hM : ProEtale.DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} P.Coefficient) X
          ((Scheme.sfIntrinsicDerivedEquivalence X P.Ring).inverse.obj
            ((P.compositionShiftedPullback f d).obj
              ((P.compositionShiftedPullback g e).obj K)))),
        P.coefficientValuedSmoothTrace (f ≫ g) (d + e) K hK =
          (PurityFiniteSetting.smoothCompactSupport P (f ≫ g)).map
              (P.compositionSourceIdentification f g d e K).hom ≫
            P.traceOriginCompositionInv f g _ hM ≫
            (PurityFiniteSetting.smoothCompactSupport P g).map
              (P.coefficientValuedSmoothTrace f d
                ((P.compositionShiftedPullback g e).obj K) hN) ≫
            P.coefficientValuedSmoothTrace g e K hK

/-- Clause (2): compatibility of every finite smooth trace with the finite reductions
`A_{E,n} → A_{E,m}` of thm-pur-finite-reduction-of-purity.
Source: clause (2) (blueprint: thm-pur-trace-normalization-transitivity). -/
def FiniteReductionClause (P : PurityFiniteSetting.{u}) : Prop :=
    ∀ (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
        {X' Y' : Scheme.{u}}
        [X'.Over (Spec (.of P.field.k))] [Y'.Over (Spec (.of P.field.k))]
        [LocallyOfFiniteType (X' ↘ Spec (.of P.field.k))]
        [QuasiCompact (X' ↘ Spec (.of P.field.k))]
        [IsSeparated (X' ↘ Spec (.of P.field.k))]
        [LocallyOfFiniteType (Y' ↘ Spec (.of P.field.k))]
        [QuasiCompact (Y' ↘ Spec (.of P.field.k))]
        [IsSeparated (Y' ↘ Spec (.of P.field.k))]
        (h : X' ⟶ Y') [h.IsOver (Spec (.of P.field.k))]
        [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
        (r : ℕ) [SmoothOfRelativeDimension r h]
        (K : Scheme.proEtaleDerivedCategory Y' P.Ring)
        (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y' K),
      (P.finiteReduction m hm hmn Y').map (P.coefficientValuedSmoothTrace h r K hK) =
        P.finiteReductionCompactSupportComparison m hm hmn h
            ((P.compositionShiftedPullback h r).obj K) ≫
          ((P.finiteReductionSetting m hm).smoothCompactSupport h).map
            (P.finiteReductionSourceComparison m hm hmn h r K).hom ≫
          (P.finiteReductionSetting m hm).coefficientValuedSmoothTrace h r
            ((P.finiteReduction m hm hmn Y').obj K)
            (P.finiteReduction_preserves_ctf m hm hmn Y' K hK)

/-- Clause (3) at the node's finite coefficients `Λ = A_{E,n}`: the finite smooth traces
`Tr^sm` of def-pur-smooth-trace (`coefficientValuedSmoothTrace`) are compatible with
arbitrary base change `v : Y' → Y` of the target, for every Cartesian square
`u, f', f, v` of finite-type `k`-schemes with `f` smooth separated of relative dimension `d`:
`v^*(Tr_{f,K}) = Tr_{f',v^*K} ∘ Rf'_!(b) ∘ B`, where `B` is the finite compact-support
base-change exchange in `smoothCompactSupport` coordinates
(`finiteCompactSupportBaseChange`, on the etale-origin pullback of the source) and `b` is the
canonical pullback/twist source identification of def-pur-smooth-pullback-exchange
(`finiteReductionBaseChangeSource`); `v^*K` is again in `D^b_ctf`.
Source: "the smooth traces are compatible with arbitrary base change of Z"
(blueprint: thm-pur-trace-normalization-transitivity). -/
def FiniteBaseChangeClause (P : PurityFiniteSetting.{u}) : Prop :=
    ∀ {X X' Y Y' : Scheme.{u}}
        [X.Over (Spec (.of P.field.k))] [X'.Over (Spec (.of P.field.k))]
        [Y.Over (Spec (.of P.field.k))] [Y'.Over (Spec (.of P.field.k))]
        [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
        [QuasiCompact (X ↘ Spec (.of P.field.k))]
        [LocallyOfFiniteType (X' ↘ Spec (.of P.field.k))]
        [QuasiCompact (X' ↘ Spec (.of P.field.k))]
        [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
        [QuasiCompact (Y ↘ Spec (.of P.field.k))]
        [LocallyOfFiniteType (Y' ↘ Spec (.of P.field.k))]
        [QuasiCompact (Y' ↘ Spec (.of P.field.k))]
        (u : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (v : Y' ⟶ Y)
        [u.IsOver (Spec (.of P.field.k))] [v.IsOver (Spec (.of P.field.k))]
        [f.IsOver (Spec (.of P.field.k))] [f'.IsOver (Spec (.of P.field.k))]
        [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
        [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
        (sq : IsPullback u f' f v) (d : ℕ)
        [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension d f']
        (K : Scheme.proEtaleDerivedCategory Y P.Ring)
        (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K),
      ∃ hM : ProEtale.DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} P.Coefficient) X'
          ((ProEtale.sfFixedDerivedPullback P.Ring u).obj
            ((Scheme.sfIntrinsicDerivedEquivalence X P.Ring).inverse.obj
              ((P.compositionShiftedPullback f d).obj K))),
        (P.finiteReductionPullback v).map (P.coefficientValuedSmoothTrace f d K hK) =
          P.finiteCompactSupportBaseChange u f' f v sq
              ((P.compositionShiftedPullback f d).obj K) hM ≫
            (PurityFiniteSetting.smoothCompactSupport P f').map
              (P.finiteReductionBaseChangeSource u f' f v sq d K).hom ≫
            P.coefficientValuedSmoothTrace f' d ((P.finiteReductionPullback v).obj K)
              (P.finiteReductionBaseChangeInput (v := v) K hK)

/-- Clause (5) at the node's finite coefficients `Λ = A_{E,n}`: on `p_d : A^d → Spec k` over
the geometric point `Spec k`, the finite unit smooth trace `Tr^sm_{p_d,Λ}` of
def-pur-smooth-trace sends the compactly supported class of the ordered product of the
Cartier classes of the coordinate zero sections (`AffineZeroPurity.supportedClass`) to `1`,
and that of the ordered product of the Kummer orientation classes `∂κ(t_i)`
(`AffineZeroPurity.kummerSupportedClass`) to `(-1)^d`. The finite level is written, as in
cor-pur-affine-space-zero-section-purity, as `setting P (P.level - 1)`, the same setting
with level `P.level - 1 + 1 = P.level`.
Source: clause (5) (blueprint: thm-pur-trace-normalization-transitivity). -/
def FiniteNormalizationClause (P : PurityFiniteSetting.{u}) : Prop :=
    ∀ d : ℕ,
      PurityFiniteSetting.finiteAffineTraceValue P (P.level - 1) d
          (ProEtale.AffineZeroPurity.supportedClass P (P.level - 1)
            (Spec (.of P.field.k)) (𝟙 _) d) = 𝟙 _ ∧
        PurityFiniteSetting.finiteAffineTraceValue P (P.level - 1) d
          (ProEtale.AffineZeroPurity.kummerSupportedClass P (P.level - 1)
            (Spec (.of P.field.k)) (𝟙 _) d) = (-1 : ℤ) ^ d • 𝟙 _

end WeilConjectures.SmoothTraceNormalization
