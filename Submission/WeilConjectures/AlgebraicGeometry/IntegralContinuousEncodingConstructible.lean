/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Submission.WeilConjectures.AlgebraicGeometry.AdicLisseModule
public import Submission.WeilConjectures.AlgebraicGeometry.ContinuousCoefficientModuleEncoding
public import Submission.WeilConjectures.AlgebraicGeometry.LatticeSheafLocallyConstant
public import Submission.WeilConjectures.ConstructibleSheaf.Defs
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ConstantFieldFlat
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FiniteFreeInternalHomExact
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedDirectImagePairingLax
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import Submission.WeilConjectures.Algebra.Homology.BoundedExactTermHomQuasiIso
import Submission.WeilConjectures.Algebra.Homology.CochainTensorModelRigidity
import Submission.WeilConjectures.Algebra.Homology.DerivedCategory.AdicTower
import Submission.WeilConjectures.Algebra.Homology.ExtensionKFlatQuasiIso
import Submission.WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized
import Submission.WeilConjectures.Algebra.Homology.KernelShiftedMappingCone
import Submission.WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExists
import Submission.WeilConjectures.Algebra.Homology.PrincipalConeExactEquivalence
import Submission.WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import Submission.WeilConjectures.Algebra.Homology.RingIsomorphismTensorTransport
import Submission.WeilConjectures.Algebra.Homology.RingPseudoCoherentSummand
import Submission.WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import Submission.WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import Submission.WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import Submission.WeilConjectures.Algebra.Homology.SplitPerfectTensorKInjective
import Submission.WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientNormalization
import Submission.WeilConjectures.AlgebraicGeometry.CoefficientConstantTowerRoosComparison
import Submission.WeilConjectures.AlgebraicGeometry.CompactSupportComparisonUnit
import Submission.WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
import Submission.WeilConjectures.AlgebraicGeometry.ConstantModelStratificationTransport
import Submission.WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCompletion
import Submission.WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import Submission.WeilConjectures.AlgebraicGeometry.EtaleRestrictScalarsFunctorComparisons
import Submission.WeilConjectures.AlgebraicGeometry.ExactProductFunctorStrictLimit
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Submission.WeilConjectures.AlgebraicGeometry.IntegralCoefficientCompletenessTransport
import Submission.WeilConjectures.AlgebraicGeometry.IntegralCompletedConstantModelTransport
import all Submission.WeilConjectures.AlgebraicGeometry.IntegralConstantModelHeartClosure
import all Submission.WeilConjectures.AlgebraicGeometry.IntegralCriterionReductions
import Submission.WeilConjectures.AlgebraicGeometry.IntegralDerivedOperationsOnSlices
import Submission.WeilConjectures.AlgebraicGeometry.IntegralLfpConstantModelComparison
import Submission.WeilConjectures.AlgebraicGeometry.IntegralSectionLocalModels
import Submission.WeilConjectures.AlgebraicGeometry.NilpotentCoefficientLissity
import Submission.WeilConjectures.AlgebraicGeometry.NilpotentReductionLissity
import Submission.WeilConjectures.AlgebraicGeometry.NoetherianStratumDetection
import Submission.WeilConjectures.AlgebraicGeometry.NormalizedDVRKFlatTransition
import Submission.WeilConjectures.AlgebraicGeometry.PbcCompletedPullbackActual
import Submission.WeilConjectures.AlgebraicGeometry.PrincipalConeKoszulRoosComparison
import Submission.WeilConjectures.AlgebraicGeometry.PrincipalIdealLocalTestCriterion
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedInverseImageEvaluation
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAlgebraicInverseImage
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleClassicalSheavesImage
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleConstantModuleEncoding
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleFiniteConstantRepresentable
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleFiniteLocalConstancyReflection
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleInverseImageLimitsZariskiLocal
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleLocalDerivedRestrictionComparisons
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageComparison
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageUnderlying
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageUnitComparison
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleMultiplicationDifferenceCriterion
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleTensorPullbackModels
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleTorAmplitude
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleTorLocalGlobal
import Submission.WeilConjectures.AlgebraicGeometry.ProetaleQcqsFpSectionCalculus
import Submission.WeilConjectures.AlgebraicGeometry.ProfiniteLocallyConstantAdjunction
import Submission.WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import Submission.WeilConjectures.AlgebraicGeometry.ProjectionFormulaArrows
import Submission.WeilConjectures.AlgebraicGeometry.PullbackTensorResolvingComputation
import Submission.WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Submission.WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackUnitExistence
import Submission.WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullbackIndependent
import Submission.WeilConjectures.AlgebraicGeometry.RingedTopoiInverseImagePairing
import Submission.WeilConjectures.AlgebraicGeometry.RingedTopoiInverseImageTensorComparison
import Submission.WeilConjectures.AlgebraicGeometry.RingedTopoiTensorComparisonConstruction
import Submission.WeilConjectures.AlgebraicGeometry.SemilinearGeometryDerived
import Submission.WeilConjectures.AlgebraicGeometry.SemilinearModuleAdjunction
import Submission.WeilConjectures.AlgebraicGeometry.SfbPerfectModelComplexComparison
import Submission.WeilConjectures.AlgebraicGeometry.SiteDerivedTensorRestriction
import Submission.WeilConjectures.AlgebraicGeometry.StrictConstantTowerOperations
import Submission.WeilConjectures.AlgebraicGeometry.StrictTowerOperations
import Submission.WeilConjectures.AlgebraicGeometry.TensorPullbackRepresentativeDescent
import Submission.WeilConjectures.AlgebraicGeometry.WeilCompletedRealizationRegular
import Submission.WeilConjectures.CategoryTheory.ExactCoupleConvergence
import Submission.WeilConjectures.CategoryTheory.ImageFiltration
import Submission.WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits
import Mathlib.Data.Int.Interval
import Submission.WeilConjectures.CategoryTheory.HalfPlaneWeakConvergence
import Submission.WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.AdjointFunctors
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionMateTranspose
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.CochainAdjunctionCompatibility
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.CochainHomotopyComparison
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.ResolvingAdjunction
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RingPseudoCoherentFiniteTorPerfect
import Submission.WeilConjectures.CategoryTheory.DerivedCoupleFunctoriality
import Submission.WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import Submission.WeilConjectures.CategoryTheory.EquivalenceAdjunctionComparison
import Submission.WeilConjectures.CategoryTheory.ExactDerivedAdjunction
import Submission.WeilConjectures.CategoryTheory.DerivedCoupleExact
import Submission.WeilConjectures.CategoryTheory.GeometricModuleConstruction
import Submission.WeilConjectures.CategoryTheory.GeometricModuleTransport
import Submission.WeilConjectures.CategoryTheory.GrothendieckDerivedCoproducts
import Submission.WeilConjectures.CategoryTheory.HalfPlaneConvergence
import Submission.WeilConjectures.CategoryTheory.HalfPlaneDiagonalColimits
import Submission.WeilConjectures.CategoryTheory.LeftDerivedKanSourceTriangles
import Submission.WeilConjectures.CategoryTheory.ModuleInverseImageUnitComparison
import Submission.WeilConjectures.CategoryTheory.NativeRingedRestrictionDerivedHom
import Submission.WeilConjectures.CategoryTheory.NativeRingedRestrictionLocalization
import Submission.WeilConjectures.CategoryTheory.NativeRingedRestrictionSlices
import Submission.WeilConjectures.CategoryTheory.NormalizedGradedFiniteKernel
import Submission.WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift
import Submission.WeilConjectures.CategoryTheory.RingedCechKoszulComparisonOnSite
import Submission.WeilConjectures.CategoryTheory.RingedKoszulCompletionReflector
import Submission.WeilConjectures.CategoryTheory.RingedNegativeKoszulDuality
import Submission.WeilConjectures.CategoryTheory.RingedPullbackPresentationOnSites
import Submission.WeilConjectures.CategoryTheory.RingedSliceExtensionTensor
import Submission.WeilConjectures.CategoryTheory.RingedSliceExtensionTensorHomData
import Submission.WeilConjectures.CategoryTheory.RoosComparisonHorizontalCoherence
import Submission.WeilConjectures.CategoryTheory.ScalarInverseImageIndependent
import Submission.WeilConjectures.CategoryTheory.ScalarLocalizationRegularColimit
import Submission.WeilConjectures.CategoryTheory.SectionActionInternal
import Submission.WeilConjectures.CategoryTheory.SiteAlgebraicCompositionUnit
import Submission.WeilConjectures.CategoryTheory.Sites.FreeModuleUniversalProperty
import Submission.WeilConjectures.CategoryTheory.Sites.GeometricInverseImageExact
import Submission.WeilConjectures.CategoryTheory.StrictRoosDerivation
import Submission.WeilConjectures.CategoryTheory.StrictRoosDerivedLimitComparison
import Submission.WeilConjectures.CategoryTheory.TowerSplitEnvelope
import Submission.WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsExistence
import Submission.WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Existence
import Submission.WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Exists
import Submission.WeilConjectures.CategoryTheory.Triangulated.MilnorSequence
import Submission.WeilConjectures.CategoryTheory.TruncationCouple
import Submission.WeilConjectures.CategoryTheory.TruncationTriangle
import Submission.WeilConjectures.CategoryTheory.UnitPowerCompleteness
import Submission.WeilConjectures.Mathlib.CategoryTheory.Adjunction.Restrict
import Submission.WeilConjectures.NumberTheory.Padics.AdicLimitFiniteModules
import Submission.WeilConjectures.RingTheory.AdicCompletionNoetherianOfQuotient
import Submission.WeilConjectures.RingTheory.FactorsThroughLocalization
import Submission.WeilConjectures.RingTheory.FilteredColimitOfFactorization
import Submission.WeilConjectures.RingTheory.FiniteProjectiveComplexFreeModel
import Submission.WeilConjectures.RingTheory.PseudoCoherentNormalizedAlgebraTower
import Submission.WeilConjectures.SecSmoothPurity.CochainInverseComparison
import Submission.WeilConjectures.SecSmoothPurity.CochainPullbackTensorCoherence
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalarsLowerStar
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.LocalVanishing

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

set_option linter.privateModule false

/-! # Constructibility under continuous integral section encoding

Source: Bhatt--Scholze, Definition 6.8.10; Stacks Project, Tag 00YV.
(auxiliary; not a blueprint node)
-/

@[expose] public section
set_option autoImplicit false
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] upperStarFromPoint
  WeilConjectures.completedIntegralCoefficientSheafUnrestricted
  Scheme.integralDetailedCoefficientComparison

attribute [local instance 100000] Sheaf.monoidalCategory Sheaf.braidedCategory

private noncomputable def pointIntegerIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    Mon.mk (integralCondensedRing l E) ≅ Mon.mk (DerivedNakayama.integerRing l E) := by
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let e : latticeCoefficientIntegers l E ≃+* Padic.coefficientExtensionIntegers l E :=
    RingEquiv.restrict (WithAbs.equiv (Padic.coefficientExtensionAbsoluteValue l E))
      _ _ (fun _ ↦ Iff.rfl)
  have he : Isometry e := by
    apply AddMonoidHomClass.isometry_of_norm e
    intro x
    rfl
  have hi : Isometry e.symm := by
    intro x y
    simpa only [e.apply_symm_apply] using (he (e.symm x) (e.symm y)).symm
  let c : Profinite.continuousMapRingSheafOfUniverse (latticeCoefficientIntegers l E) ≅
      DerivedNakayama.integerRingSheaf l E :=
    { hom := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((e.toRingHom.compLeftContinuous S.unop he.continuous).comp
              ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
      inv := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((e.symm.toRingHom.compLeftContinuous S.unop hi.continuous).comp
              ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
      hom_inv_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact e.symm_apply_apply _
      inv_hom_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact e.apply_symm_apply _ }
  let cAb := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso c
  have : IsMonHom cAb.hom := Sheaf.isMonHom_sheafCompose_map _ c.hom
  have : IsMonHom cAb.inv := Sheaf.isMonHom_sheafCompose_map _ c.inv
  exact
    { hom := Mon.ofHom cAb.hom
      inv := Mon.ofHom cAb.inv
      hom_inv_id := by apply Mon.Hom.ext; exact cAb.hom_inv_id
      inv_hom_id := by apply Mon.Hom.ext; exact cAb.inv_hom_id }

attribute [local irreducible] pointIntegerIso

private theorem integral_internal_constant_models
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [EssentiallySmall.{u + 1} X.ProEt] [IsNoetherian X]
    (M : AdicCompletion.Modules l E X)
    (hM : IsConstructibleModuleObject (AdicCompletion.ring l E X) M) :
    IsConstantModelConstructible (DerivedNakayama.integerRing l E) X M := by
  let e := pointIntegerIso l E
  let φ := e.hom.hom
  let ψ := coefficientMap φ X
  have h := integralLfpConstantModelComparison l E X ((Mod.comap ψ).obj M)
  exact (constantModel_comap_iff φ X M).mp
    (h.mp (_root_.constructible_comap ψ hM))

end AlgebraicGeometry.ProEtale
