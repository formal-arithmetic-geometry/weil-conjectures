/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.IntegralDirectImageTower
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedEquivalence
public import WeilConjectures.AlgebraicGeometry.SpTowerGamma.SmoothPurityTowerGammaData
public import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerGluingData
import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekInterfaces
import WeilConjectures.AlgebraicGeometry.SpChartAdmissibility.SmoothPurityTowerChartData
import WeilConjectures.AlgebraicGeometry.VaryingRingGraph.VaryingRingGraphSummand
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowersAbelian
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Localization.Predicate
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalization
import WeilConjectures.Compactification.CategoryBaseChange
import WeilConjectures.AlgebraicGeometry.SmoothPurity.CompactifiableCompatibleTower
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenCalculus
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.Algebra.Homology.Ringed.RingedOpenTotalTensorKFlat
import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenMatePasting
import WeilConjectures.AlgebraicGeometry.VaryingRing.SemilinearScalarRestriction
import WeilConjectures.AlgebraicGeometry.SmoothPurity.ChartNormalizedModelIdentification
import WeilConjectures.AlgebraicGeometry.ProperOpenCalculus.CompactificationRefinementCoherence
import WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.EtaleProEtaleCoefficientCompatibility
import WeilConjectures.AlgebraicGeometry.AdjunctionTransfer.EtaleCtfChartDomain
import WeilConjectures.CategoryTheory.ExactDerivedPasting.Word.ExactDerivedTransformationPasting
import WeilConjectures.AlgebraicGeometry.Finite.Compact.FiniteCompactSupportDomains
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.TowerGeometryAdjunctionEvaluation
import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingProperOpenPasting
import WeilConjectures.CategoryTheory.RingedSliceExtensionExactness
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.SmoothPurity.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.Compactification.Dense
import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityEtaleNormalization
import WeilConjectures.AlgebraicGeometry.SpCoordinateAdjunction.SmoothPurityCoordinateRightComparisons
import WeilConjectures.AlgebraicGeometry.SpChartAdmissibility.SmoothPurityTowerChartAdmissibility
import WeilConjectures.AlgebraicGeometry.SpTowerP1.SmoothPurityTowerP1Adjunction
import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceTower
import WeilConjectures.AlgebraicGeometry.SpCoordinateAdjunction.SmoothPurityCoordinateCategories
import WeilConjectures.AlgebraicGeometry.SmoothOfRelativeDimension.SmoothAdmissibleCoordinateCover
import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerBinaryPairGluing
import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerPairOpenRestriction2
import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerLocalCounitRepresentability
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalRealization
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalChart
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalConservativity
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImage
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.SmoothPurityMap
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothPurityMaps
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.SpTowerP1.TowerP1CoefficientCoordinates
public import WeilConjectures.AlgebraicGeometry.SpTowerP1.TowerP1GeometricCoordinates
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothTensorDuality
public import WeilConjectures.AlgebraicGeometry.Finite.General.FiniteGeneralRing
public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekCalculus
public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerTransitionCompatibility
public import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekLevels
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowers
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedTowers
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.PurityDiagonalDualizingObject
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.SpChartAdmissibility.SmoothPurityTowerBoundsOperations
public import WeilConjectures.Algebra.Homology.ProperBaseChange.KFlatResolutionGeneral
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.AlgebraicGeometry.SmoothPurity.TowerOperationsGroundFieldRetagging
import WeilConjectures.AlgebraicGeometry.SpFiniteOrientation.FiniteOrientationReduction
import WeilConjectures.SmoothPurity.Finite.FiniteLineTensorConditions
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.AlgebraicGeometry.Finite.FiniteLocallyFreeLineModels
import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorRealization
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryMonoidal
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonTorInterval
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.SpTowerProjection.TowerCompactSupportProjectionFormula
public import Mathlib.FieldTheory.Finite.Basic
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalSmoothnessFiniteComparison
public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekData
public import WeilConjectures.AlgebraicGeometry.SpTowerMate.SmoothPurityTowerMateEvaluationReduction
public import WeilConjectures.AlgebraicGeometry.SpIntegralAdjunction.IntegralReconstructionComparisonData
public import WeilConjectures.AlgebraicGeometry.IntegralReconstructionComparisons.IntegralReconstructionComparisons
public import WeilConjectures.AlgebraicGeometry.Picard.SpTwistedPullback.TwistedPullbackReductionData
public import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerBound
public import WeilConjectures.SmoothPurity.IntegralLineReduction.IntegralLineReductionRestriction
public import WeilConjectures.SmoothPurity.Integral.IntegralPullbackSystemComparison
public import WeilConjectures.SmoothPurity.Pur.PurReductionLimitShiftAdjunction
public import WeilConjectures.Algebra.Homology.Signed.SignedLineScalarTensorTower
public import WeilConjectures.AlgebraicGeometry.Picard.IntegralStrictReductionModel
public import WeilConjectures.SmoothPurity.Adic.AdicPuritySourceReduction
public import WeilConjectures.SmoothPurity.Supporting.SignedTwistFirstReduction
public import WeilConjectures.SmoothPurity.Supporting.SignedLineTensorEquivalence
public import WeilConjectures.Algebra.Homology.LineUnbounded.LineUnboundedDerivedTensor
public import WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.Picard.SpTwistedPullback.TwistedPullbackLineMembership
public import Mathlib.Algebra.CharP.CharAndCard
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
public import WeilConjectures.AlgebraicGeometry.CompleteCompactificationLimit.CompleteCompactificationLimitSupport
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import WeilConjectures.AlgebraicGeometry.CompleteCompactificationLimit.CompleteCompactificationLimitRealization
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantExact
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitudeProEtaleModule
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModuleIntrinsicComparison
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Sf.SfFiniteExceptionalInverseImage
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.SmoothBaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralModels
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEquivalence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportComposition
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompBaseChangeDefs
public import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
public import WeilConjectures.SmoothPurity.Integral.Twist.IntegralTwistBaseChangeDefinitions
import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarPullbackNormalization
import WeilConjectures.SmoothPurity.StrictQuotient.QuotientExpressionKFlatNormalization
import WeilConjectures.AlgebraicGeometry.Completed.CompletedLineDerived
import WeilConjectures.CategoryTheory.RingedDerivedComparisons.RingedDerivedMonoidalComparisons

/-! # Native integral reduction, Tate sources, and compact-support exchange

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-purity-bc/sk-prop-sp-purity-bc.proof.md, opening integral paragraph;
DAG comparison refinement, steps 1--8
(blueprint: lem-pur-native-integral-reduction-exchange).

All tower arrows live in the ordinary derived category of strict systems. A natural
index n denotes the positive exponent n+1. The section equivalence is the published
one and every coefficient transition is the actual quotient map.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpNativeIntegralReduction

open IntegralDirectImageTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The resolving complexes used by the recorded reduction counits.
Source: proof steps 2 and 5, flat-term K-flat resolutions
(blueprint: lem-pur-native-integral-reduction-exchange). -/
def Good (T : Scheme.{u}) (P : CochainComplex (Modules l E T) ℤ) : Prop :=
  CochainComplex.IsKFlatIndependentCoefficients (R := spIntegralSectionRing l E T)
    (((spIntegralModuleEquivalence l E T).functor.mapHomologicalComplex (.up ℤ)).obj P) ∧
  ∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := ProEt.topology T)
    (R := spIntegralSectionRing l E T)
    ((spIntegralModuleEquivalence l E T).functor.obj (P.X i))

set_option maxHeartbeats 0 in
-- Elaborating the section-normalized comparisons retains their full dependent types.
/-- The balanced scalar/tensor comparison on entire system complexes, fixed on every
local tensor summand and by the two localization counits. This is normalization data
for the comparison in this node, not another tensor construction.
Source: proof step 5 (blueprint: lem-pur-native-integral-reduction-exchange). -/
structure TensorReduction (s : Presentation l E) (T : Scheme.{u}) where
  comparison : MonoidalCategory.tensor (Integral l E T) ⋙ derivedReduction l E s T ≅
    (derivedReduction l E s T).prod (derivedReduction l E s T) ⋙
      SpTowerShriek.tensor l E s.base T
  chain : ∀ P Q : CochainComplex (Modules l E T) ℤ,
    ((ordinaryReduction l E s T).mapHomologicalComplex (.up ℤ)).obj (P ⊗ Q) ≅
      (SemilinearSections.totalTensor.{u + 1, u, u + 1}
        (coefficientSequenceTopology (ProEt.topology T))
        (SemilinearSections.systemRing (ProEt.topology T)
          (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T))).obj
        (((ordinaryReduction l E s T).mapHomologicalComplex (.up ℤ)).obj P,
          ((ordinaryReduction l E s T).mapHomologicalComplex (.up ℤ)).obj Q)
  pure : ∀ (P Q : CochainComplex (Modules l E T) ℤ)
    (p q k : ℤ) (hpq : p + q = k) (n : ℕ) (U : T.ProEtᵒᵖ)
    (x : (P.X p).X.obj.obj U) (y : (Q.X q).X.obj.obj U)
    (b : (SpTowerShriek.B l E T n).obj.obj U)
    (e : Evaluation l E s),
    ((chain P Q).hom.f k).val.app (op (n, U.unop))
      (((ordinaryReductionEvaluation l E s e T n).inv.app ((P ⊗ Q).X k)).val.app U
        (SheafOfModules.systemModelTmul ((s.towers T).scalar
          (spIntegralReductionScalar l E T (s.reduction T).coefficient n)).model
          ((spIntegralModuleEquivalence l E T).functor.obj ((P ⊗ Q).X k)) U b
          (((CochainComplex.ιMapBifunctor P Q (curriedTensor _) p q k hpq).hom.hom.app U)
            (InternalAbelianSheafModule.comparison_internalTmul (ProEt.topology T)
              (condensedRingObj (spIntegralCondensed l E) T) (P.X p) (Q.X q) U x y)))) =
    (SemilinearSections.tensorSummand.{u + 1, u, u + 1}
      (coefficientSequenceTopology (ProEt.topology T))
      (SemilinearSections.systemRing (ProEt.topology T)
        (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T))
      (((ordinaryReduction l E s T).mapHomologicalComplex (.up ℤ)).obj P)
      (((ordinaryReduction l E s T).mapHomologicalComplex (.up ℤ)).obj Q) p q k hpq).val.app
      (op (n, U.unop))
      (SemilinearSections.tensorSection.{u + 1, u, u + 1}
        (coefficientSequenceTopology (ProEt.topology T))
        (SemilinearSections.systemRing (ProEt.topology T)
          (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T))
        ((ordinaryReduction l E s T).obj (P.X p))
        ((ordinaryReduction l E s T).obj (Q.X q)) (op (n, U.unop))
        (((ordinaryReductionEvaluation l E s e T n).inv.app (P.X p)).val.app U
          (SheafOfModules.systemModelTmul ((s.towers T).scalar
            (spIntegralReductionScalar l E T (s.reduction T).coefficient n)).model
            ((spIntegralModuleEquivalence l E T).functor.obj (P.X p)) U b x))
        (((ordinaryReductionEvaluation l E s e T n).inv.app (Q.X q)).val.app U
          (SheafOfModules.systemModelTmul ((s.towers T).scalar
            (spIntegralReductionScalar l E T (s.reduction T).coefficient n)).model
            ((spIntegralModuleEquivalence l E T).functor.obj (Q.X q)) U 1 y)))
  kflat : ∀ P : CochainComplex (Modules l E T) ℤ, Good l E T P →
    CochainComplex.IsKFlatIndependentCoefficients
      (R := SemilinearSections.systemRing (ProEt.topology T)
        (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T))
      (((ordinaryReduction l E s T).mapHomologicalComplex (.up ℤ)).obj P)
  representatives : ∀ (P Q : CochainComplex (Modules l E T) ℤ)
    (hP : Good l E T P) (hQ : Good l E T Q),
    (derivedReduction l E s T).map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
        reductionComplexComparison l E s T (P ⊗ Q) ≫ DerivedCategory.Q.map (chain P Q).hom ≫
        ((s.base.calculus T).tensorModels.iso
          (coefficientSequenceTopology (ProEt.topology T))
          (SemilinearSections.systemRing (ProEt.topology T)
            (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T))
          (s.base.calculus T).closed _ _ (kflat P hP) (kflat Q hQ)).hom =
      comparison.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        (SpTowerShriek.tensor l E s.base T).map
          (Prod.mkHom (reductionComplexComparison l E s T P)
            (reductionComplexComparison l E s T Q))

set_option maxHeartbeats 0 in
-- Elaborating the section-normalized comparisons retains their full dependent types.
set_option maxHeartbeats 0 in
-- Elaborating the section-normalized comparisons retains their full dependent types.
set_option maxHeartbeats 0 in
-- Elaborating the section-normalized comparisons retains their full dependent types.
end AlgebraicGeometry.ProEtale.SpNativeIntegralReduction
