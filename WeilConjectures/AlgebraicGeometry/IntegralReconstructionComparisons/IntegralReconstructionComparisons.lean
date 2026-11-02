/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowers
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedTowers
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedEquivalence
public import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerGluingData
public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekData
public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekInterfaces
public import WeilConjectures.AlgebraicGeometry.SpChartAdmissibility.SmoothPurityTowerChartData
public import WeilConjectures.AlgebraicGeometry.VaryingRingGraph.VaryingRingGraphSummand
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowersAbelian
public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekCalculus
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Localization.Predicate
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImage
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalization
public import WeilConjectures.Compactification.CategoryBaseChange
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.CompactifiableCompatibleTower
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenCalculus
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonTorInterval
public import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerTransitionCompatibility
public import WeilConjectures.Algebra.Homology.Ringed.RingedOpenTotalTensorKFlat
public import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenMatePasting
public import WeilConjectures.AlgebraicGeometry.VaryingRing.SemilinearScalarRestriction
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.ChartNormalizedModelIdentification
public import WeilConjectures.AlgebraicGeometry.ProperOpenCalculus.CompactificationRefinementCoherence
public import WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.EtaleProEtaleCoefficientCompatibility
public import WeilConjectures.AlgebraicGeometry.AdjunctionTransfer.EtaleCtfChartDomain
public import WeilConjectures.CategoryTheory.ExactDerivedPasting.Word.ExactDerivedTransformationPasting
public import WeilConjectures.AlgebraicGeometry.Finite.Compact.FiniteCompactSupportDomains
public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.TowerGeometryAdjunctionEvaluation
public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingProperOpenPasting
public import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
public import WeilConjectures.CategoryTheory.RingedSliceExtensionExactness
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.SmoothPurity.ProEtaleWeaklyEtaleLocalization
public import WeilConjectures.Compactification.Dense
public import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityEtaleNormalization
public import WeilConjectures.AlgebraicGeometry.SpCoordinateAdjunction.SmoothPurityCoordinateRightComparisons
public import WeilConjectures.AlgebraicGeometry.SpChartAdmissibility.SmoothPurityTowerChartAdmissibility
public import WeilConjectures.AlgebraicGeometry.SpTowerP1.SmoothPurityTowerP1Adjunction
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceTower
public import WeilConjectures.AlgebraicGeometry.SpCoordinateAdjunction.SmoothPurityCoordinateCategories
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteCtfTriangulated
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.TowerOpenCover.TowerOpenCoverTriangleData
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExact
public import WeilConjectures.Algebra.Homology.OpenDerivedMatePresentation
public import WeilConjectures.Algebra.Homology.OpenCoverMateComplexShortExact
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenComparison
public import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionRingIsoSupplement
public import WeilConjectures.Algebra.Homology.SubterminalLocal.SubterminalModuleLocalCalculus
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.RingedRestrictionExchange.ProEtaleRingedOpenCoverReflectsIso
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.TowerOpenAdjunctionEvaluation
public import WeilConjectures.Algebra.Homology.RingedOpenScalar.RingedOpenScalarAdjunction
public import WeilConjectures.SixFunctors.Supporting.PullbackTorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
public import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory
public import Mathlib.CategoryTheory.Triangulated.Yoneda
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
public import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalRealization
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalChart
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalConservativity
public import WeilConjectures.AlgebraicGeometry.CompleteCompactificationLimit.CompleteCompactificationLimitSupport
import WeilConjectures.AlgebraicGeometry.CompleteCompactificationLimit.CompleteCompactificationLimitRealization
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerGluingData
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekData
import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekInterfaces
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedTowers
import WeilConjectures.AlgebraicGeometry.SpChartAdmissibility.SmoothPurityTowerChartData
import WeilConjectures.AlgebraicGeometry.VaryingRingGraph.VaryingRingGraphSummand
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowersAbelian
import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekCalculus
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Localization.Predicate
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImage
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalization
import WeilConjectures.Compactification.CategoryBaseChange
import WeilConjectures.AlgebraicGeometry.SmoothPurity.CompactifiableCompatibleTower
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenCalculus
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
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
import WeilConjectures.Compactification.Dense
import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityEtaleNormalization
import WeilConjectures.AlgebraicGeometry.SpCoordinateAdjunction.SmoothPurityCoordinateRightComparisons
import WeilConjectures.AlgebraicGeometry.SpChartAdmissibility.SmoothPurityTowerChartAdmissibility
import WeilConjectures.AlgebraicGeometry.SpTowerP1.SmoothPurityTowerP1Adjunction
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceTower
import WeilConjectures.AlgebraicGeometry.SpCoordinateAdjunction.SmoothPurityCoordinateCategories
import WeilConjectures.AlgebraicGeometry.Finite.FiniteCtfTriangulated
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.TowerOpenCover.TowerOpenCoverTriangleData
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExact
import WeilConjectures.Algebra.Homology.OpenDerivedMatePresentation
import WeilConjectures.Algebra.Homology.OpenCoverMateComplexShortExact
import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenComparison
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionRingIsoSupplement
import WeilConjectures.Algebra.Homology.SubterminalLocal.SubterminalModuleLocalCalculus
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.AlgebraicGeometry.RingedRestrictionExchange.ProEtaleRingedOpenCoverReflectsIso
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.TowerOpenAdjunctionEvaluation
import WeilConjectures.Algebra.Homology.RingedOpenScalar.RingedOpenScalarAdjunction
import WeilConjectures.SixFunctors.Supporting.PullbackTorAmplitude
import WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory
import Mathlib.CategoryTheory.Triangulated.Yoneda
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalRealization
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalChart
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalConservativity
import WeilConjectures.SmoothPurity.PurityFiniteSetting.SmoothPurityMap
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothPurityMaps
import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
import WeilConjectures.AlgebraicGeometry.SpTowerP1.TowerP1CoefficientCoordinates
import WeilConjectures.AlgebraicGeometry.SpTowerP1.TowerP1GeometricCoordinates
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothTensorDuality
import WeilConjectures.AlgebraicGeometry.Finite.General.FiniteGeneralRing
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekLevels
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowers
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.PurityDiagonalDualizingObject
import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.SpChartAdmissibility.SmoothPurityTowerBoundsOperations
import WeilConjectures.Algebra.Homology.ProperBaseChange.KFlatResolutionGeneral
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.AlgebraicGeometry.SmoothPurity.TowerOperationsGroundFieldRetagging
import WeilConjectures.AlgebraicGeometry.SpFiniteOrientation.FiniteOrientationReduction
import WeilConjectures.SmoothPurity.Finite.FiniteLineTensorConditions
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.AlgebraicGeometry.Finite.FiniteLocallyFreeLineModels
import WeilConjectures.SmoothPurity.Supporting.SignedLineTensorEquivalence
import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorRealization
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryMonoidal
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.SpTowerProjection.TowerCompactSupportProjectionFormula
import Mathlib.FieldTheory.Finite.Basic
import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalSmoothnessFiniteComparison
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Natural integral reconstruction comparisons

Source: current blueprint, sec-smooth-purity/sk-prop-sp-integral-adjunction,
Normalization and Bijections in sk-prop-sp-integral-adjunction-bijection.proof.md
(blueprint: lem-sp-integral-reconstruction-comparisons).

The original strict-tower category is retained. Section-model coordinate changes below
are localizations of the given ordinary equivalences and their units and counits.
The comparison b is reduction of the canonical compactification-limit comparison,
followed by the actual reconstruction counit, as a map of entire strict towers.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.IntegralReconstructionComparisons
open CompleteCompactificationLimit

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The exact-open localization of the specified ordinary section-coordinate word.
Source: blueprint, compactification comparison
(blueprint: lem-sp-integral-reconstruction-comparisons). -/
def openCoordinates (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (DX : SpCoefficientTowersAbelian l E X) (DZ : SpCoefficientTowersAbelian l E Z) :
    towerOpen l E b o j DX DZ ≅
      (SpTowerCalculus.realization l E b X DX).functor ⋙
        SpTowerShriek.openD l E b (o.openOp j) ⋙
          (SpTowerCalculus.realization l E b Z DZ).inverse := by
  letI := DX.hasDerived
  letI := DZ.hasDerived
  letI := b.realizationAdditive X
  letI := Functor.additive_of_preserves_binary_products (b.realization Z).inverse
  exact Functor.mapDerivedCategoryCompIso (b.realization X).functor
      ((o.openOp j).extension ⋙ (b.realization Z).inverse) ≪≫
    Functor.isoWhiskerLeft _
      (Functor.mapDerivedCategoryCompIso (o.openOp j).extension (b.realization Z).inverse)

/-- The direct-image coordinate word, using uniqueness of right derived functors.
Both outer equivalences are exact; the first preserves K-injectives.
Source: blueprint, compactification comparison
(blueprint: lem-sp-integral-reconstruction-comparisons). -/
def pushCoordinates (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    (DZ : SpCoefficientTowersAbelian l E Z) (DY : SpCoefficientTowersAbelian l E Y) :
    towerPush l E b o p DZ DY ≅
      (SpTowerCalculus.realization l E b Z DZ).functor ⋙
        SpTowerShriek.push l E b (o.geometry p) ⋙
          (SpTowerCalculus.realization l E b Y DY).inverse := by
  letI := DZ.hasDerived
  letI := DY.hasDerived
  letI := DZ.grothendieck
  letI := b.realizationAdditive Z
  letI := Functor.additive_of_preserves_binary_products (b.realization Y).inverse
  exact Functor.mapDerivedCategoryCompRightDerivedFunctorIso (b.realization Z).functor
      ((o.geometry p).push ⋙ (b.realization Y).inverse) ≪≫
    Functor.isoWhiskerLeft _
      (Functor.rightDerivedFunctorCompMapDerivedCategoryIso
        (o.geometry p).push (b.realization Y).inverse)

/-- Cancel the intermediate section equivalence by its actual counit. This compares
entire strict derived-tower functors, without selecting maps from finite evaluations.
Source: blueprint, compactification comparison
(blueprint: lem-sp-integral-reconstruction-comparisons). -/
def supportCoordinates (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (D : ∀ T : Scheme.{u}, SpCoefficientTowersAbelian l E T)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    towerOpen l E b o c.i (D X) (D c.Z) ⋙ towerPush l E b o c.g (D c.Z) (D Y) ≅
      SpTowerCalculus.compactSupport l E b o D c :=
  Functor.isoWhiskerRight (openCoordinates l E b o c.i (D X) (D c.Z)) _ ≪≫
    Functor.isoWhiskerLeft _ (pushCoordinates l E b o c.g (D c.Z) (D Y)) ≪≫
    Functor.isoWhiskerLeft
      ((SpTowerCalculus.realization l E b X (D X)).functor ⋙
        SpTowerShriek.openD l E b (o.openOp c.i))
      (Functor.isoWhiskerRight (SpTowerCalculus.realization l E b c.Z (D c.Z)).counitIso
        (SpTowerShriek.push l E b (o.geometry c.g) ⋙
          (SpTowerCalculus.realization l E b Y (D Y)).inverse))

/-- The canonical compactification-limit word, followed by the fixed coordinate
comparison. All factors are actual natural transformations of strict-tower functors.
Source: blueprint, alpha_M in Bijections
(blueprint: lem-sp-integral-reconstruction-comparisons). -/
def realization (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (D : ∀ T : Scheme.{u}, SpCoefficientTowersAbelian l E T)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (rX : SpReductionTower l E X (D X)) (rZ : SpReductionTower l E c.Z (D c.Z))
    (rY : SpReductionTower l E Y (D Y))
    (aX : LimitPresentation l E X (D X) rX)
    (aZ : LimitPresentation l E c.Z (D c.Z) rZ)
    (aY : LimitPresentation l E Y (D Y) rY)
    (e : forgetting l E X (D X) ⋙ fixedOpenOrd l E c.i ≅
      ordinaryTowerOpen l E b o c.i ⋙ forgetting l E c.Z (D c.Z))
    (d : forgetDerived l E c.Z (D c.Z) rZ aZ ⋙ (fixedPushOrd l E c.g).rightDerivedFunctor ≅
      towerPush l E b o c.g (D c.Z) (D Y) ⋙ forgetDerived l E Y (D Y) rY aY) :
    image l E c ⟶ reduction l E X (D X) rX ⋙
      SpTowerCalculus.compactSupport l E b o D c ⋙ totalLimit l E Y (D Y) rY aY :=
  comparison l E b o c (D X) (D c.Z) (D Y) rX rZ rY aX aZ aY e d ≫
    Functor.whiskerLeft (reduction l E X (D X) rX)
      (Functor.whiskerRight (supportCoordinates l E b o D c).hom
        (totalLimit l E Y (D Y) rY aY))

end AlgebraicGeometry.ProEtale.IntegralReconstructionComparisons
