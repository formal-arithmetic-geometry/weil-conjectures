/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ConstantFieldFlat
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FiniteFreeInternalHomExact
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
public import Submission.WeilConjectures.Algebra.Homology.BoundedExactTermHomQuasiIso
public import Submission.WeilConjectures.Algebra.Homology.CochainTensorModelRigidity
public import Submission.WeilConjectures.Algebra.Homology.DerivedCategory.AdicTower
public import Submission.WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized
public import Submission.WeilConjectures.Algebra.Homology.KernelShiftedMappingCone
public import Submission.WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExists
public import Submission.WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import Submission.WeilConjectures.Algebra.Homology.RingIsomorphismTensorTransport
public import Submission.WeilConjectures.Algebra.Homology.RingPseudoCoherentSummand
public import Submission.WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
public import Submission.WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
public import Submission.WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
public import Submission.WeilConjectures.Algebra.Homology.SplitPerfectTensorKInjective
public import Submission.WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientNormalization
public import Submission.WeilConjectures.AlgebraicGeometry.CoefficientConstantTowerRoosComparison
public import Submission.WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
public import Submission.WeilConjectures.AlgebraicGeometry.ConstantModelStratificationTransport
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleRestrictScalarsFunctorComparisons
public import Submission.WeilConjectures.AlgebraicGeometry.ExactProductFunctorStrictLimit
public import Submission.WeilConjectures.AlgebraicGeometry.ExtendedCechCompletionModel
public import Submission.WeilConjectures.AlgebraicGeometry.GeometricStalkColimits
public import Submission.WeilConjectures.AlgebraicGeometry.IntegralCoefficientCompletenessTransport
public import Submission.WeilConjectures.AlgebraicGeometry.IntegralCompletedConstantModelTransport
public import Submission.WeilConjectures.AlgebraicGeometry.IntegralConstantCompletion
public import Submission.WeilConjectures.AlgebraicGeometry.IntegralCriterionReductions
public import Submission.WeilConjectures.AlgebraicGeometry.NilpotentCoefficientLissity
public import Submission.WeilConjectures.AlgebraicGeometry.NilpotentReductionLissity
public import Submission.WeilConjectures.AlgebraicGeometry.NoetherianStratumDetection
public import Submission.WeilConjectures.AlgebraicGeometry.PbcCompletedPullbackActual
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedInverseImageEvaluation
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ClosedSiteAdjunction
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAlgebraicInverseImage
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleClassicalSheavesImage
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleFiniteLocalConstancyReflection
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleInverseImageLimitsZariskiLocal
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleLocalDerivedRestrictionComparisons
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageComparison
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageUnderlying
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageUnitComparison
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleMultiplicationDifferenceCriterion
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleTorLocalGlobal
public import Submission.WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import Submission.WeilConjectures.AlgebraicGeometry.RingedLocalizationRestriction
public import Submission.WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullbackIndependent
public import Submission.WeilConjectures.AlgebraicGeometry.RingedTopoiTensorComparisonConstruction
public import Submission.WeilConjectures.AlgebraicGeometry.SemilinearGeometryDerived
public import Submission.WeilConjectures.AlgebraicGeometry.SemilinearModuleAdjunction
public import Submission.WeilConjectures.AlgebraicGeometry.SfbPerfectModelComplexComparison
public import Submission.WeilConjectures.AlgebraicGeometry.StrictConstantTowerOperations
public import Submission.WeilConjectures.AlgebraicGeometry.StrictTowerOperations
public import Submission.WeilConjectures.AlgebraicGeometry.WeilCompletedRealizationRegular
public import Submission.WeilConjectures.CategoryTheory.AbutmentImageFiltration
public import Submission.WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
public import Submission.WeilConjectures.CategoryTheory.AdjunctionSquareComposition
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.AdjointFunctors
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionMateTranspose
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.CochainAdjunctionCompatibility
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.ResolvingAdjunction
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RingPseudoCoherentFiniteTorPerfect
public import Submission.WeilConjectures.CategoryTheory.DerivedCoupleFunctoriality
public import Submission.WeilConjectures.CategoryTheory.DerivedModuleDirectSums
public import Submission.WeilConjectures.CategoryTheory.EquivalenceAdjunctionComparison
public import Submission.WeilConjectures.CategoryTheory.ExactDerivedAdjunction
public import Submission.WeilConjectures.CategoryTheory.FinitePageGradedQuotient
public import Submission.WeilConjectures.CategoryTheory.GeometricModuleConstruction
public import Submission.WeilConjectures.CategoryTheory.GeometricModuleTransport
public import Submission.WeilConjectures.CategoryTheory.HalfPlaneConvergence
public import Submission.WeilConjectures.CategoryTheory.HalfPlaneDiagonalColimits
public import Submission.WeilConjectures.CategoryTheory.LeftDerivedKanSourceTriangles
public import Submission.WeilConjectures.CategoryTheory.ModuleInverseImageUnitComparison
public import Submission.WeilConjectures.CategoryTheory.NativeRingedRestrictionDerivedHom
public import Submission.WeilConjectures.CategoryTheory.NativeRingedRestrictionLocalization
public import Submission.WeilConjectures.CategoryTheory.NativeRingedRestrictionSlices
public import Submission.WeilConjectures.CategoryTheory.NormalizedGradedFiniteKernel
public import Submission.WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift
public import Submission.WeilConjectures.CategoryTheory.RingedCechKoszulComparisonOnSite
public import Submission.WeilConjectures.CategoryTheory.RingedKoszulCompletionReflector
public import Submission.WeilConjectures.CategoryTheory.RingedNegativeKoszulDuality
public import Submission.WeilConjectures.CategoryTheory.RingedPullbackPresentationOnSites
public import Submission.WeilConjectures.CategoryTheory.RoosComparisonHorizontalCoherence
public import Submission.WeilConjectures.CategoryTheory.ScalarInverseImageIndependent
public import Submission.WeilConjectures.CategoryTheory.ScalarLocalizationRegularColimit
public import Submission.WeilConjectures.CategoryTheory.Sites.FreeModuleUniversalProperty
public import Submission.WeilConjectures.CategoryTheory.StrictRoosDerivation
public import Submission.WeilConjectures.CategoryTheory.StrictRoosDerivedLimitComparison
public import Submission.WeilConjectures.CategoryTheory.TowerSplitEnvelope
public import Submission.WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsExistence
public import Submission.WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Existence
public import Submission.WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Exists
public import Submission.WeilConjectures.CategoryTheory.Triangulated.MilnorSequence
public import Submission.WeilConjectures.CategoryTheory.TruncationCouple
public import Submission.WeilConjectures.CategoryTheory.TruncationTriangle
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Adjunction.Restrict
public import Submission.WeilConjectures.NumberTheory.Padics.AdicLimitFiniteModules
public import Submission.WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
public import Submission.WeilConjectures.RingTheory.AdicCompletionNoetherianOfQuotient
public import Submission.WeilConjectures.RingTheory.FactorsThroughLocalization
public import Submission.WeilConjectures.RingTheory.FilteredColimitOfFactorization
public import Submission.WeilConjectures.RingTheory.FiniteProjectiveComplexFreeModel
public import Submission.WeilConjectures.RingTheory.PseudoCoherentNormalizedAlgebraTower
public import Submission.WeilConjectures.SecSmoothPurity.CochainInverseComparison
public import Submission.WeilConjectures.SecSmoothPurity.CochainPullbackTensorCoherence
public import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ModuleDerivedCategory
public import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalarsLowerStar
public import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.LocalVanishing
import all Submission.WeilConjectures.AlgebraicGeometry.IntegralCriterionReductions

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Canonical integral constant-model realization

Source: Bhatt--Scholze, Definition 6.8.10 and Proposition 6.8.11(3), and the
projection-normalized integral coefficient comparison.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint

namespace AlgebraicGeometry.ProEtale.IntegralConstantModel

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The spectral and absolute-value coefficient presentations have the same ring object.
Source: the projection-normalized integral coefficient comparison
(auxiliary; not a blueprint node). -/
theorem pointEquality :
    Mon.mk (DerivedNakayama.integerRing l E) = sfbCondensedIntegers l E :=
  integralPointMon_eq l E

/-- The identity comparison of the two equal point coefficient presentations.
Source: the spectral-norm integral coefficient comparison
(auxiliary; not a blueprint node). -/
def pointComparison : Mon.mk (DerivedNakayama.integerRing l E) ≅ sfbCondensedIntegers l E :=
  eqToIso (pointEquality l E)

/-- The actual section-and-coefficient functor; its action changes only scalar actions.
Source: the normalized coefficient projections of the integral criterion
(auxiliary; not a blueprint node). -/
def modulesFunctor (X : Scheme.{u}) :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (sfbCondensedIntegers l E).X X) ⥤
      Scheme.proEtaleRingModules X
        (Scheme.adicLisseCompletedRing X (Scheme.pbcIntegralDatum l E).ideal) :=
  Mod.comap (coefficientMap (pointComparison l E).hom.hom X) ⋙
    integralSectionFunctor l E X ⋙
    SheafOfModules.restrictScalars.{u + 1}
      (Scheme.integralDetailedCoefficientComparison X l E).hom ⋙
    Scheme.pbcRestrict (Scheme.pbcCompletedComparison X (Scheme.pbcIntegralDatum l E)).hom

/-- Each coefficient map used by the functor is an isomorphism.
Source: the finite-projection integral coefficient comparisons
(auxiliary; not a blueprint node). -/
instance modulesFunctor_isEquivalence (X : Scheme.{u}) :
    (modulesFunctor l E X).IsEquivalence := by
  have : (Mod.comap (coefficientMap (pointComparison l E).hom.hom X)).IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso
      (coefficientMap (pointComparison l E).hom.hom X)).isEquivalence_functor
  have : (Scheme.pbcRestrict
      (Scheme.pbcCompletedComparison X (Scheme.pbcIntegralDatum l E)).hom).IsEquivalence :=
    restriction_isEquivalence ((Scheme.adicLisseForget X).mapIso
      (Scheme.pbcCompletedComparison X (Scheme.pbcIntegralDatum l E)))
  have : (integralSectionFunctor l E X).IsEquivalence :=
    (integralSectionFunctor_properties l E X).2
  have : (SheafOfModules.restrictScalars.{u + 1}
      (Scheme.integralDetailedCoefficientComparison X l E).hom).IsEquivalence :=
    restriction_isEquivalence (Scheme.integralDetailedCoefficientComparison X l E)
  unfold modulesFunctor
  exact Functor.isEquivalence_trans _ _

/-- The ordinary realization preserves addition, since all its factors preserve products.
Source: Stacks Tag 00YV
(auxiliary; not a blueprint node). -/
instance modulesFunctor_additive (X : Scheme.{u}) : (modulesFunctor l E X).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Termwise localization of the canonical ordinary realization.
Source: Stacks Tags 00YV and 05RU
(auxiliary; not a blueprint node). -/
def derived (X : Scheme.{u}) := (modulesFunctor l E X).mapDerivedCategory.asEquivalence

end AlgebraicGeometry.ProEtale.IntegralConstantModel
