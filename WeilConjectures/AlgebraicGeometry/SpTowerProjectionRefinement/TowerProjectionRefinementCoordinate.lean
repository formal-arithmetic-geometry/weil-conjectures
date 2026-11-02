/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Finite.General.FiniteGeneralRing
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowers
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowersAbelian
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedTowers
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalSmoothnessFiniteComparison
public import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerGluingData
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerBound
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalRealization
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalChart
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalConservativity
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImage
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.SmoothPurityMap
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothPurityMaps
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
public import WeilConjectures.AlgebraicGeometry.SpTowerP1.TowerP1CoefficientCoordinates
public import WeilConjectures.AlgebraicGeometry.SpTowerP1.TowerP1GeometricCoordinates
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothTensorDuality
public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekCalculus
public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerTransitionCompatibility
public import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekLevels
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.PurityDiagonalDualizingObject
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.SpChartAdmissibility.SmoothPurityTowerBoundsOperations
public import WeilConjectures.Algebra.Homology.ProperBaseChange.KFlatResolutionGeneral
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonTorInterval
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.SpTowerProjection.TowerCompactSupportProjectionFormula
public import Mathlib.FieldTheory.Finite.Basic
public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekData
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.Finite.Compact.FiniteCompactSiteCoherence
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitudePresentations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteLocalizingExceptionalPreservation
public import Mathlib.CategoryTheory.Adjunction.Unique
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.IntegralDirectImageTower
public import WeilConjectures.AlgebraicGeometry.CompleteCompactificationLimit.CompleteCompactificationLimitRealization
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.AlgebraicGeometry.IntegralReconstructionComparisons.IntegralReconstructionComparisons
public import WeilConjectures.AlgebraicGeometry.Picard.SpTwistedPullback.TwistedPullbackReductionData
public import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedEquivalence
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
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import Mathlib.Algebra.Field.ULift
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.AlgebraicGeometry.ProEtaleFixedModuleLocalConstancy
public import WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
public import WeilConjectures.AlgebraicGeometry.ProEtaleLisseFiniteModelsFromLisse
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelLocalConstancy
public import WeilConjectures.SmoothPurity.ProEtaleFiniteModelStalks
public import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorRealization
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryMonoidal
public import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.AlgebraicGeometry.SpFiniteOrientation.FiniteOrientationReduction
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothLevelOfOrientation
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantOpenSquareExchange
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
public import WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleExceptionalObjectComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingCompactSupportProjectionMap
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperProjectionFormula
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalDirectImagePreservation
public import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageMateCompatibility
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImageCanonicalMate
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImage
public import WeilConjectures.AlgebraicGeometry.Classical.ClassicalContinuityMapSupplement
public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedDirectImageComparisonMap
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedDirectImageBoundedBelow
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalBounds
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.ModuleSheafConstantRingEquivalence
public import WeilConjectures.CategoryTheory.Sites.InjectivePresheafModuleCechCocycleLiftMax
public import WeilConjectures.CategoryTheory.InjectiveModulePresheaf
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import WeilConjectures.AlgebraicGeometry.EtaleCechVanishingCriterion
public import WeilConjectures.AlgebraicGeometry.EtaleSiteCechComplexComparison
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorUpperBound
public import WeilConjectures.AlgebraicGeometry.ProEtale.Replete
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftComplete
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjComparison
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat
public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekInterfaces
public import WeilConjectures.AlgebraicGeometry.FiniteRingSiteTensorTransposeData
public import WeilConjectures.Algebra.Homology.System.SystemDerivedSubsequence
public import WeilConjectures.Algebra.Homology.System.SystemRingedSequenceSite
public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemOperations
public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralCompactificationRealizationData
public import WeilConjectures.Algebra.Homology.System.SystemLevelLeftExtensionBasic
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.ExactDerivedAdjunctionSupplement
public import WeilConjectures.CategoryTheory.StrictTowerArithmetic.StrictTowerArithmeticRestrictionDefs
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.CompactifiableOverField

/-! # Tensor and projection in coefficient coordinates

All functors below act in the original coefficient derived categories, as does
`SpTowerCalculus.F`. The projection uses the prescribed proper/open arrow and
only the counits of the fixed realization equivalences.
(blueprint: def-sp-tower-projection-refinement-coordinates)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.SpTowerProjectionRefinement

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
  (q : SpTowerCalculus.Coordinates l E b)

/-- Tensor by a fixed tower, expressed in coefficient coordinates.
Source: realization transport (blueprint: def-sp-tower-projection-refinement-coordinates). -/
def coefficientTensor (Y : Scheme.{u}) (L : SpTowerShriek.D l E Y) :=
  (SpTowerCalculus.realization l E b Y (q.abelian Y)).functor ⋙
    Prod.sectL (SpTowerShriek.D l E Y) L ⋙ SpTowerShriek.tensor l E b Y ⋙
      (SpTowerCalculus.realization l E b Y (q.abelian Y)).inverse

/-- Tensor by the fixed pullback, in coefficient coordinates.
Source: realization transport (blueprint: def-sp-tower-projection-refinement-coordinates). -/
def coefficientTensorPull {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : SpTowerShriek.D l E Y) :=
  coefficientTensor l E b q X ((SpTowerShriek.pull l E b (o.geometry f)).obj L)

/-- The C-level projection. Its endpoints use the actual C-level compact-support
functor. The two counits identify those endpoints with the proper/open tensor
word before applying the inverse realization to that word.
Source: the proper/open projection map, Stacks 0B56
(blueprint: def-sp-tower-projection-refinement-coordinates). -/
def coefficientProjection {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (K : spDerivedCoefficientTowers l E X (q.abelian X))
    (L : SpTowerShriek.D l E Y) :
    (coefficientTensor l E b q Y L).obj ((SpTowerCalculus.F l E b o q c).obj K) ⟶
      (SpTowerCalculus.F l E b o q c).obj
        ((coefficientTensorPull l E b o q f L).obj K) :=
  (SpTowerCalculus.realization l E b Y (q.abelian Y)).inverse.map
    ((SpTowerShriek.tensor l E b Y).map
        (Prod.mkHom ((SpTowerCalculus.realization l E b Y (q.abelian Y)).counitIso.hom.app
          ((SpTowerShriek.F l E b o c).obj
            ((SpTowerCalculus.realization l E b X (q.abelian X)).functor.obj K))) (𝟙 L)) ≫
      SpTowerShriek.projection l E b o c
        ((SpTowerCalculus.realization l E b X (q.abelian X)).functor.obj K) L ≫
      (SpTowerShriek.F l E b o c).map
        ((SpTowerCalculus.realization l E b X (q.abelian X)).counitIso.inv.app
          ((SpTowerShriek.tensor l E b X).obj
            (((SpTowerCalculus.realization l E b X (q.abelian X)).functor.obj K),
              (SpTowerShriek.pull l E b (o.geometry f)).obj L))))

end AlgebraicGeometry.ProEtale.SpTowerProjectionRefinement
