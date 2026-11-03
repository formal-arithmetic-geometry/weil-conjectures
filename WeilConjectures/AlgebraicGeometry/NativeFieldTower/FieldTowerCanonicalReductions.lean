/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekInterfaces
public import WeilConjectures.AlgebraicGeometry.SpCondensedIntegralAdjunction.IntegralAdjunctionBijectionStatement
public import WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import WeilConjectures.Algebra.Homology.System.SystemScalarCoherence
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImage
public import WeilConjectures.AlgebraicGeometry.ReductionExceptionalStatement
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityReductionTowerData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportCompact
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorComparison
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Shift.Adjunction
public import WeilConjectures.CategoryTheory.Right.RightExactTensorShiftCancellation
public import WeilConjectures.CategoryTheory.Derived.DerivedTensorRightExact
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleDerivedFunctorCompositorShifts
public import WeilConjectures.AlgebraicGeometry.IntegralModelsStatement
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralModels
public import WeilConjectures.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousCoefficientModuleEncodingSupplement
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicIntegersInvertEll
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationMap
public import Mathlib.RingTheory.Localization.BaseChange
public import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralPushComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralModel
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
public import WeilConjectures.SixFunctors.Integral.IntegralModelsGenerators
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.PadicIntegersBoundedTriangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Bounded.BoundedConstructiblePushforwardRestriction
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
public import WeilConjectures.Compactification.NagataCompactification
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.CategoryTheory.SmoothPurity.ComplexColimitHomotopyColimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedContinuitySections
public import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedContinuityDirectImage
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.Compactification.BoundaryRefinement
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
public import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import Mathlib.CategoryTheory.Linear.Yoneda
public import WeilConjectures.AlgebraicGeometry.IntegralConstructibleSheafHom
public import WeilConjectures.CategoryTheory.HomColimitExtension
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralLfpConstantModelComparison
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
public import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.Topology.NoetherianSpace
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteModelStratumFiltration
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Order.CompletePartialOrder
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartLisseExtensionConstructible
public import WeilConjectures.SixFunctors.TopologicalLisseIntegralClosure
public import WeilConjectures.SixFunctors.TopologicalIntegralConstructibility
public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalization
public import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
public import WeilConjectures.Compactification.Dense
public import WeilConjectures.AlgebraicGeometry.CondensedIntegralTower.CondensedCoefficientTowers
public import WeilConjectures.AlgebraicGeometry.CondensedIntegralTower.CondensedNormalizedTowers
public import WeilConjectures.Algebra.Homology.Strict.StrictProjectionLimitData
public import WeilConjectures.ProperBaseChange.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.Integral.Constant.IntegralConstantModelRealizationSupplement
public import WeilConjectures.NumberTheory.Padics.LocalFieldIntegralBasis
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientsFiniteFree
public import WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
public import WeilConjectures.AlgebraicGeometry.ExactProductFunctorStrictLimit
public import WeilConjectures.CategoryTheory.Sites.FixedCoefficientDerivedChangeOfRings
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import WeilConjectures.AlgebraicGeometry.ReductionDirectImageFiniteCoefficients
public import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerGluingData
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerBound
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekData
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedTowers
import WeilConjectures.AlgebraicGeometry.SpChartAdmissibility.SmoothPurityTowerChartData
import WeilConjectures.AlgebraicGeometry.VaryingRingGraph.VaryingRingGraphSummand
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowersAbelian
import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekCalculus
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
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonTorInterval
import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerTransitionCompatibility
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
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.CategoryTheory.RingedSliceExtensionExactness
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.SmoothPurity.ProEtaleWeaklyEtaleLocalization
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
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionCompatibilities
public import WeilConjectures.Algebra.Homology.RingedTensorSquare.RingedExchangeTensorCoherence
public import WeilConjectures.AlgebraicGeometry.SmoothPurityReductionTowerIntegralHeart
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.Topology.Algebra.Ring.Ideal

/-! # Canonical reductions for a finite extension of coefficient fields

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-setup/sec-the-purity-statement/sk-thm-purity-transport/
sk-lem-sp-field-extension/sk-lem-sp-field-extension-towers.md and .proof.md,
clause (1) and proof (1) (the scalar/reduction square is the simultaneous tensor
associator), on the tower data of det-sp-field-extension-tower-data and the canonical
finite encodings of det-sp-finite-quotient-canonical-encoding.

* `NativeFieldTower.ReductionLevel` (blueprint: det-sp-reduction-level-native-comparison);
* `NativeFieldTower.FiniteScalarLevel`
  (blueprint: det-sp-tower-scalar-level-native-comparison);
* `NativeFieldTower.ReductionSquareNormalized`, `reductionSquare_existsUnique`
  (blueprint: det-sp-field-tower-reduction-square-associator).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.MonObj
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
open scoped CategoryTheory.Obj TensorProduct

namespace AlgebraicGeometry.ProEtale.CondensedIntegralTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The tower coefficient ring of `SpTowerShriek` is the finite quotient of N1.
Source: (blueprint: det-sp-reduction-level-native-comparison), A_n.
Proof: `spEllIdeal` is the principal ideal of ell. -/
theorem towerRing_eq_finiteQuotient (n : ℕ) :
    SpTowerShriek.R l E n = finiteQuotient l E n := rfl

end AlgebraicGeometry.ProEtale.CondensedIntegralTower

namespace AlgebraicGeometry.ProEtale.NativeFieldTower
variable (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω]
  [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

open CondensedIntegralTower

/-- Ordinary finite-coefficient modules use the standard localization, as in
`Encoding.ordinaryDerived`. Source: (blueprint: det-sp-finite-quotient-canonical-encoding). -/
local instance ordinaryHasDerived (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] (T : Scheme.{u}) :
    HasDerivedCategory (FiniteDiscreteOrdinary.Ordinary A T) :=
  HasDerivedCategory.standard _

/-- The derived finite encoding as a functor out of native finite coefficients.
Source: (blueprint: det-sp-reduction-level-native-comparison). -/
abbrev finiteEncodingFunctor (E : Index l Ω) (n : ℕ) (T : Scheme.{u}) :=
  (finiteDerived l E.val n T).functor

/-- The section scalar model of the n-th tower level of the reduction construction.
Source: (blueprint: det-sp-reduction-level-native-comparison), M/ell^(n+1). -/
abbrev levelModel {E : Index l Ω} (s : IntegralDirectImageTower.Presentation l E.val)
    (T : Scheme.{u}) (n : ℕ) :=
  (s.towers T).scalar (spIntegralReductionScalar l E.val T (s.reduction T).coefficient n)

/-- The exact evaluation/localization comparison of the strict tower category.
Source: (blueprint: det-sp-reduction-level-native-comparison), exact evaluations. -/
def levelEvaluationFactors {E : Index l Ω} {T : Scheme.{u}}
    (D : SpCoefficientTowersAbelian l E.val T)
    (n : ℕ) :=
  letI := D.hasDerived
  letI := D.equivalenceAdditive
  letI := D.evaluationLimits n
  letI := D.evaluationColimits n
  letI : (spCoefficientEvaluation l E.val T D.equivalence n).Additive :=
    Functor.additive_of_preserves_binary_products _
  @Functor.mapDerivedCategoryFactors (spCoefficientTowers l E.val T) _ _ D.hasDerived
    (Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T
      (Padic.coefficientExtensionIntegers l E.val ⧸ spEllIdeal l E.val ^ (n + 1))))
    _ _ (HasDerivedCategory.standard _)
    (spCoefficientEvaluation l E.val T D.equivalence n) _ _ _

set_option maxHeartbeats 2000000 in
-- The record compares two dependent scalar presentations.
/-- Level-n comparison of the strict reduction tower with native derived reduction.
`level` is the level identification fixed on K-flat representatives by the
construction's ordinary level isomorphism and its universal counit; `restriction` is the
identity on sections; `comparison` is pinned by the two scalar adjunction units.
Source: (blueprint: det-sp-reduction-level-native-comparison); sk-prop-sp-integral-towers
reduction, Construction and Normalization (det-sp-reduction-tower-normalized). -/
structure ReductionLevel {E : Index l Ω} (s : IntegralDirectImageTower.Presentation l E.val)
    (T : Scheme.{u}) (n : ℕ) where
  level : (s.reduction T).red ⋙ spDerivedCoefficientEvaluation l E.val T (s.towers T) n ≅
    (levelModel l Ω s T n).model.T
  level_normalized : ∀ P : CochainComplex (spIntegralSectionModules l E.val T) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (R := spIntegralSectionRing l E.val T) P →
    (spDerivedCoefficientEvaluation l E.val T (s.towers T) n).map
        ((s.reduction T).counit.app P) ≫
      (levelEvaluationFactors l Ω (s.towers T) n).hom.app
        (((s.reduction T).ordinary.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex ((s.reduction T).level n).hom (.up ℤ)).app P) =
    level.hom.app (DerivedCategory.Q.obj P) ≫ (levelModel l Ω s T n).model.ε.app P
  restriction : Mod.comap (quotientCoefficient l Ω E n T) ⋙
      (spIntegralModuleEquivalence l E.val T).functor ≅
    (finiteEncoding l E.val n T).ordinary.functor ⋙
      SheafOfModules.restrictScalars.{u + 1}
        ((sheafCompose (Scheme.ProEt.topology T)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            (spIntegralReductionScalar l E.val T (s.reduction T).coefficient n))
  restriction_sections : ∀ (N : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (finiteRing l E.val n) T)) (U : T.ProEtᵒᵖ)
    (x : ((Mod.comap (quotientCoefficient l Ω E n T) ⋙
      (spIntegralModuleEquivalence l E.val T).functor).obj N).val.obj U)
    (y : N.X.obj.obj U), HEq x y → HEq ((restriction.hom.app N).val.app U x) y
  comparison : (Mod.extendScalars (quotientCoefficient l Ω E n T)).leftDerivedFunctor ⋙
      finiteEncodingFunctor l Ω E n T ≅
    (spIntegralModuleEquivalence l E.val T).functor.mapDerivedCategory ⋙
      (levelModel l Ω s T n).model.T
  unit : ∀ K, (spIntegralModuleEquivalence l E.val T).functor.mapDerivedCategory.map
      ((Mod.derivedExtendMapDerivedCategoryAdjunction
        (quotientCoefficient l Ω E n T)).unit.app K) ≫
      (Functor.mapDerivedCategorySquareIso restriction).hom.app
        ((Mod.extendScalars (quotientCoefficient l Ω E n T)).leftDerivedFunctor.obj K) ≫
      (SheafOfModules.restrictScalars.{u + 1}
        ((sheafCompose (Scheme.ProEt.topology T)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            (spIntegralReductionScalar l E.val T
              (s.reduction T).coefficient n))).mapDerivedCategory.map
        (comparison.hom.app K) =
    (levelModel l Ω s T n).adjunction.unit.app
      ((spIntegralModuleEquivalence l E.val T).functor.mapDerivedCategory.obj K)

/-- The canonical level-n comparison: tower level of the reduction of an internal
integral complex with the encoded native reduction `M ⊗^L O_E/ℓ^(n+1)`.
Source: (blueprint: det-sp-reduction-level-native-comparison). -/
def ReductionLevel.iso {E : Index l Ω} {s : IntegralDirectImageTower.Presentation l E.val}
    {T : Scheme.{u}} {n : ℕ} (c : ReductionLevel l Ω s T n) :
    (spIntegralModuleEquivalence l E.val T).functor.mapDerivedCategory ⋙
        (s.reduction T).red ⋙ spDerivedCoefficientEvaluation l E.val T (s.towers T) n ≅
      (Mod.extendScalars (quotientCoefficient l Ω E n T)).leftDerivedFunctor ⋙
        finiteEncodingFunctor l Ω E n T :=
  Functor.isoWhiskerLeft _ c.level ≪≫ c.comparison.symm

/-- The level comparison exists.
Source: (blueprint: det-sp-reduction-level-native-comparison).
Proof: K-flat representatives and the construction's ordinary level isomorphism give the
level identification; section reconstruction gives the restriction comparison; the mate
of its localization is invertible and satisfies the unit equation. -/
theorem reductionLevel_nonempty {E : Index l Ω}
    (s : IntegralDirectImageTower.Presentation l E.val) (T : Scheme.{u}) (n : ℕ) :
    Nonempty (ReductionLevel l Ω s T n) := by
  sorry

/-- Any two level comparisons agree.
Source: (blueprint: det-sp-reduction-level-native-comparison).
Proof: every complex is quasi-isomorphic to a K-flat one, fixing `level`; HEq on sections
fixes `restriction`; injectivity of the mate correspondence fixes `comparison`. -/
theorem reductionLevel_subsingleton {E : Index l Ω}
    (s : IntegralDirectImageTower.Presentation l E.val) (T : Scheme.{u}) (n : ℕ) :
    Subsingleton (ReductionLevel l Ω s T n) := by
  sorry

set_option maxHeartbeats 2000000 in
-- The record compares two dependent scalar presentations.
/-- Level-n comparison of finite scalar extension along `O_E/ℓ^(n+1) → O_F/ℓ^(n+1)`
with native `scalarSixChange (finitePoint n)`, fixed by the identity-on-sections
restriction comparison and the two scalar adjunction units.
Source: (blueprint: det-sp-tower-scalar-level-native-comparison). -/
structure FiniteScalarLevel {E F : Index l Ω} {n : ℕ}
    (b : (⟨finiteRing l E.val n⟩ : CondensedRing.ScalarSixRing.{u}) ⟶ ⟨finiteRing l F.val n⟩)
    (q : SpTowerShriek.R l E.val n →+* SpTowerShriek.R l F.val n) (T : Scheme.{u}) where
  restriction : Mod.comap (_root_.AlgebraicGeometry.ProEtale.coefficientMap
        (Λ := finiteRing l E.val n) (Λ' := finiteRing l F.val n) b.hom.hom T) ⋙
      (finiteEncoding l E.val n T).ordinary.functor ≅
    (finiteEncoding l F.val n T).ordinary.functor ⋙
      proEtaleRingRestrictScalars (proEtaleConstantRingMap (T := T) q)
  restriction_sections : ∀ (N : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (finiteRing l F.val n) T)) (U : T.ProEtᵒᵖ)
    (x : ((Mod.comap (_root_.AlgebraicGeometry.ProEtale.coefficientMap
        (Λ := finiteRing l E.val n) (Λ' := finiteRing l F.val n) b.hom.hom T) ⋙
      (finiteEncoding l E.val n T).ordinary.functor).obj N).val.obj U)
    (y : N.X.obj.obj U), HEq x y → HEq ((restriction.hom.app N).val.app U x) y
  comparison : CondensedRing.scalarSixChange b T ⋙ finiteEncodingFunctor l Ω F n T ≅
    finiteEncodingFunctor l Ω E n T ⋙ scalarExtensionFunctor q T
  unit : ∀ K, (finiteEncodingFunctor l Ω E n T).map
      ((Mod.derivedExtendMapDerivedCategoryAdjunction
        (_root_.AlgebraicGeometry.ProEtale.coefficientMap
          (Λ := finiteRing l E.val n) (Λ' := finiteRing l F.val n) b.hom.hom T)).unit.app K) ≫
      (Functor.mapDerivedCategorySquareIso restriction).hom.app
        ((CondensedRing.scalarSixChange b T).obj K) ≫
      (scalarRestriction q T).map (comparison.hom.app K) =
    (finiteScalarAdjunction q T).unit.app ((finiteEncodingFunctor l Ω E n T).obj K)

/-- The finite scalar comparison exists when `q` and `b` are the same inclusion.
Source: (blueprint: det-sp-tower-scalar-level-native-comparison).
Proof: the encodings carry `b` to the constant-ring map `q`, so restriction of scalars is
the identity on sections; its localized mate is invertible and satisfies the unit law. -/
theorem finiteScalarLevel_nonempty {E F : Index l Ω} (h : E ≤ F) (n : ℕ)
    (D : Models l Ω) (T : Scheme.{u}) (sT : ScalarProperties l Ω E F h T) :
    Nonempty (FiniteScalarLevel l Ω (sT.finitePoint n) ((D.coefficients E F h).quotient n) T) := by
  sorry

/-- Any two finite scalar comparisons agree.
Source: (blueprint: det-sp-tower-scalar-level-native-comparison).
Proof: HEq on sections fixes `restriction`; injectivity of the mate fixes `comparison`. -/
theorem finiteScalarLevel_subsingleton {E F : Index l Ω} {n : ℕ}
    (b : (⟨finiteRing l E.val n⟩ : CondensedRing.ScalarSixRing.{u}) ⟶ ⟨finiteRing l F.val n⟩)
    (q : SpTowerShriek.R l E.val n →+* SpTowerShriek.R l F.val n) (T : Scheme.{u}) :
    Subsingleton (FiniteScalarLevel l Ω b q T) := by
  sorry

section Square

variable (D : Models l Ω) {E F : Index l Ω} (h : E ≤ F)
  {X Z Y : Scheme.{u}} {j : X ⟶ Z} [IsOpenImmersion j]
  {p : Z ⟶ Y} [IsProper p] [QuasiCompact (j ≫ p)] [HasCompactification (j ≫ p)]
  {d : ℕ} (mE : IntegralModel l Ω D E j p d) (mF : IntegralModel l Ω D F j p d)

end Square

end AlgebraicGeometry.ProEtale.NativeFieldTower
