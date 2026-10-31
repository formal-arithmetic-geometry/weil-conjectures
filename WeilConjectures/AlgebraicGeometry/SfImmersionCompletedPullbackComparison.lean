/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.AlgebraicGeometry.PbcActualStrictPullback
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.DerivedCompleteOnSlices
public import WeilConjectures.AlgebraicGeometry.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import WeilConjectures.AlgebraicGeometry.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.AlgebraicGeometry.SfDerivedComplete
public import WeilConjectures.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.SiteInverseImageTensor
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.Limits
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedInverseImageLeftAdjoint
public import WeilConjectures.AlgebraicGeometry.IndEtaleBasisWeaklyContractibleCover
public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.CategoryTheory.Sites.LowerShriekCoveringGenerators
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import WeilConjectures.CategoryTheory.Sites.LowerShriekCorepresentability
public import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.Sheaf
public import WeilConjectures.CategoryTheory.Sites.CoveringRepresentableCoequalizer
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.Sites.RegularEpi
public import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
public import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedInverseImageEvaluation
public import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.InverseMateEquivalence
public import WeilConjectures.AlgebraicGeometry.ProEtale.Replete
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
public import WeilConjectures.AlgebraicGeometry.ProEtaleOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImageLimitsZariskiLocal
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf
public import WeilConjectures.Mathlib.CategoryTheory.NatIso
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageComparison
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageUnderlying
public import WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
public import WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
public import WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
public import WeilConjectures.CategoryTheory.ModuleInverseImageAction
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageScalarGraph
public import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresAbelian
public import WeilConjectures.CategoryTheory.StrictRoosDerivedLimitComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.SfImmersionCompletedPullbackCoreA
import all WeilConjectures.AlgebraicGeometry.SfImmersionCompletedPullbackCoreA
import WeilConjectures.AlgebraicGeometry.SfImmersionFiniteReductionInterval
import all WeilConjectures.AlgebraicGeometry.CompletedTowerPullbackSupplement
import WeilConjectures.AlgebraicGeometry.IntegralCoefficientCompletenessTransportSupplement
import WeilConjectures.AlgebraicGeometry.PbcIntrinsicTowerComplete
import all WeilConjectures.AlgebraicGeometry.PbcCompletedPullbackActualSupplement

import WeilConjectures.AlgebraicGeometry.CompletedOpenExchangeTransport
import WeilConjectures.CategoryTheory.StrictRoosModel
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Algebra.Homology.Functor
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import WeilConjectures.AlgebraicGeometry.ProEtaleProductsExact
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleSectionsLimitsColimits
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimitSupplement
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
import WeilConjectures.AlgebraicGeometry.ProEtale.SectionsConservative
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.WContractibleAffineCover
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.RingTheory.ProEtale.WContractible
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import WeilConjectures.RingTheory.IndPrincipalZariski
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import all WeilConjectures.AlgebraicGeometry.SfImmersionFiniteNormalization
import all WeilConjectures.AlgebraicGeometry.SfImmersionRoosNormalization
import all WeilConjectures.AlgebraicGeometry.WeilTensorProduct
import all WeilConjectures.AlgebraicGeometry.AdicCoefficientDatumSupplement
import all WeilConjectures.CategoryTheory.ExactAdjointTowerModels
import all WeilConjectures.CategoryTheory.RoosTensorNormalization
import WeilConjectures.CategoryTheory.UnboundedExactAdjunctionSquare
import all WeilConjectures.AlgebraicGeometry.ExactProductFunctorStrictLimit
import all WeilConjectures.CategoryTheory.StrictRoosComparison
import all WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.CategoryTheory.Preadditive.Injective.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all WeilConjectures.CategoryTheory.StrictRoosDerivation
import all WeilConjectures.Algebra.Homology.RoosComplex
import all WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import all Mathlib.CategoryTheory.Adjunction.Evaluation
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import all WeilConjectures.CategoryTheory.StrictRoosNormalization
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import all Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import all Mathlib.Logic.Denumerable
import all WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosChainMaps
import all WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosDescent
import all WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosResolution
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all Mathlib.Algebra.Homology.DerivedCategory.KInjective
import all Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosCompatibility

/-! # Ordinary immersion pullback and strict completed pullback

Source: localization Step 6; Stacks Tags 09AA, 099M and 099N (2),(5).
The canonical coefficient constructions are reexported from CoreA; strict tower
and Roos constructions remain in this module.
-/

@[expose] public noncomputable section
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section NormalizationProofs

attribute [-instance] CategoryTheory.ringedConstantTowerModulesAbelian
attribute [-instance] CategoryTheory.ringedConstantTowerTowersAbelian
attribute [-instance] CategoryTheory.ringedConstantTowerAdditive
attribute [-instance] CategoryTheory.strictTowerConstantAdditive
attribute [-instance] CategoryTheory.strictTowerLimitAdditive

attribute [local irreducible] AlgebraicGeometry.Scheme.AdicCoefficients.ringSystem
attribute [local irreducible] CategoryTheory.Limits.limit
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale WeilConjectures

namespace ImmersionRoosMateProof
universe v d
open CategoryTheory.RoosTensor
variable {A B : Type (v + 1)} [Category.{v} A] [Category.{v} B]
  [Abelian A] [Abelian B] [HasCountableProducts A] [HasCountableProducts B]
  [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
  [HasDerivedCategory.{d} A] [HasDerivedCategory.{d} B]
  [HasDerivedCategory.{d} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{d} (ℕᵒᵖ ⥤ B)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
  [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ B)]
  [(lim : (ℕᵒᵖ ⥤ A) ⥤ A).Additive] [(lim : (ℕᵒᵖ ⥤ B) ⥤ B).Additive]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesLimitsOfShape ℕᵒᵖ F]
  [PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ A B).obj F)]
  [PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ A B).obj F)]

private theorem derivedUnit_isIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions C] (G : C ⥤ D) [G.Additive]
    (I : CochainComplex C ℤ) [I.IsKInjective] :
    IsIso (G.rightDerivedFunctorUnitQ I) := by
  rw [Functor.rightDerivedFunctorUnitQ_eq]
  exact inferInstanceAs (IsIso (G.rightDerivedFunctorObjQIso I).inv)

private theorem roos_normalized_square
    (κA : roosF (A := A) ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙
      (lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctor)
    (κB : roosF (A := B) ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙
      (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctor)
    (hA : ∀ K, DerivedCategory.Q.map (roosι K) ≫ κA.hom.app K =
      DerivedCategory.Q.map
        (limit.isoLimitCone ⟨HomologicalComplex.coneOfHasLimitEval K.asFunctor,
          HomologicalComplex.isLimitConeOfHasLimitEval K.asFunctor⟩).hom ≫
        (lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctorUnitQ K)
    (hB : ∀ K, DerivedCategory.Q.map (roosι K) ≫ κB.hom.app K =
      DerivedCategory.Q.map
        (limit.isoLimitCone ⟨HomologicalComplex.coneOfHasLimitEval K.asFunctor,
          HomologicalComplex.isLimitConeOfHasLimitEval K.asFunctor⟩).hom ≫
        (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctorUnitQ K)
    (β : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctor ⋙ F.mapDerivedCategory ⟶
      ((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapDerivedCategory ⋙
        (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctor)
    (hn : ∀ K, F.mapDerivedCategory.map
        ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctorUnitQ K) ≫
        β.app (DerivedCategory.Q.obj K) ≫
        (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctor.map
          (((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapDerivedCategoryFactors.hom.app K) =
      F.mapDerivedCategoryFactors.hom.app
          (((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (preservesLimitNatIso (J := ℕᵒᵖ) F).hom (.up ℤ)).app K) ≫
        (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctorUnitQ ((roosTowerAction F).obj K))
    (K : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    F.mapDerivedCategory.map (κA.hom.app K) ≫ β.app (DerivedCategory.Q.obj K) =
      F.mapDerivedCategoryFactors.hom.app (roosF.obj K) ≫
        DerivedCategory.Q.map (roosAdditiveComparison F K) ≫
        κB.hom.app ((roosTowerAction F).obj K) ≫
        (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctor.map
          (((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapDerivedCategoryFactors.inv.app K) := by
  let HA : (ℕᵒᵖ ⥤ A) ⥤ A := lim
  let HB : (ℕᵒᵖ ⥤ B) ⥤ B := lim
  let T := towerF F
  let TC := roosTowerAction F
  let FD := F.mapDerivedCategory
  let θ : roosF ⋙ complexF F ⟶ TC ⋙ roosF :=
    { app := roosAdditiveComparison F
      naturality := fun _ _ f ↦ roosAdditiveComparison_natural F f }
  let S := DerivedCategory.Q ⋙ T.mapDerivedCategory ⋙ HB.rightDerivedFunctor
  let δ : roosF ⋙ DerivedCategory.Q ⋙ FD ⟶ S :=
    Functor.whiskerRight κA.hom FD ≫ Functor.whiskerLeft DerivedCategory.Q β
  let δ' : roosF ⋙ DerivedCategory.Q ⋙ FD ⟶ S :=
    Functor.whiskerLeft roosF F.mapDerivedCategoryFactors.hom ≫
      Functor.whiskerRight θ DerivedCategory.Q ≫
      Functor.whiskerLeft TC κB.hom ≫
      Functor.whiskerRight T.mapDerivedCategoryFactors.inv HB.rightDerivedFunctor
  have hδ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective] :
      δ.app I = δ'.app I := by
    have hu : IsIso (HA.rightDerivedFunctorUnitQ I) := derivedUnit_isIso HA I
    have hlim : IsIso (DerivedCategory.Q.map ((strictTowerLimitIso).hom.app I)) :=
      inferInstanceAs (IsIso (DerivedCategory.Q.mapIso ((strictTowerLimitIso).app I)).hom)
    have hi : IsIso (DerivedCategory.Q.map (roosι I) ≫ κA.hom.app I) := by
      rw [hA]
      infer_instance
    have : IsIso (DerivedCategory.Q.map (roosι I)) :=
      IsIso.of_isIso_comp_right _ (κA.hom.app I)
    apply (cancel_epi (FD.map (DerivedCategory.Q.map (roosι I)))).mp
    dsimp only [δ, δ', NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app]
    rw [← FD.map_comp_assoc, hA, FD.map_comp, Category.assoc]
    have hh := hn I
    apply (cancel_mono (HB.rightDerivedFunctor.map (T.mapDerivedCategoryFactors.hom.app I))).mp
    simp only [Category.assoc, ← HB.rightDerivedFunctor.map_comp,
      Iso.inv_hom_id_app, HB.rightDerivedFunctor.map_id]
    erw [Category.comp_id, hh]
    have hf := F.mapDerivedCategoryFactors.hom.naturality (roosι I)
    change FD.map (DerivedCategory.Q.map (roosι I)) ≫
        F.mapDerivedCategoryFactors.hom.app (roosF.obj I) =
      F.mapDerivedCategoryFactors.hom.app (limit I.asFunctor) ≫
        DerivedCategory.Q.map ((complexF F).map (roosι I)) at hf
    erw [reassoc_of% hf, ← DerivedCategory.Q.map_comp_assoc, comparison_inclusion,
      DerivedCategory.Q.map_comp, Category.assoc, hB]
    have hf' := F.mapDerivedCategoryFactors.hom.naturality
      ((strictTowerLimitIso).hom.app I)
    change FD.map (DerivedCategory.Q.map ((strictTowerLimitIso).hom.app I)) ≫
        F.mapDerivedCategoryFactors.hom.app ((HA.mapHomologicalComplex (.up ℤ)).obj I) =
      F.mapDerivedCategoryFactors.hom.app (limit I.asFunctor) ≫
        DerivedCategory.Q.map ((complexF F).map ((strictTowerLimitIso).hom.app I)) at hf'
    erw [reassoc_of% hf', ← DerivedCategory.Q.map_comp_assoc, comparison_limitIso,
      DerivedCategory.Q.map_comp]
    simp only [Category.assoc]
    rfl
  obtain ⟨I, hI, j, _, hj⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective K
  have := hI
  have := hj
  have : IsIso (S.map j) := by
    change IsIso (HB.rightDerivedFunctor.map (T.mapDerivedCategory.map (DerivedCategory.Q.map j)))
    infer_instance
  have h : δ.app K = δ'.app K := by
    apply (cancel_mono (S.map j)).mp
    rw [← δ.naturality j, ← δ'.naturality j, hδ I]
  exact h

private theorem roos_normalized_square_ordinary
    (κA : roosF (A := A) ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙
      (lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctor)
    (κB : roosF (A := B) ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙
      (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctor)
    (hA : ∀ K, DerivedCategory.Q.map (roosι K) ≫ κA.hom.app K =
      DerivedCategory.Q.map
        ((ExactAdjointTowerModels.ordinaryIso (A := A)).inv.app K) ≫
        (lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctorUnitQ K)
    (hB : ∀ K, DerivedCategory.Q.map (roosι K) ≫ κB.hom.app K =
      DerivedCategory.Q.map
        ((ExactAdjointTowerModels.ordinaryIso (A := B)).inv.app K) ≫
        (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctorUnitQ K)
    (β : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctor ⋙ F.mapDerivedCategory ⟶
      ((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapDerivedCategory ⋙
        (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctor)
    (hn : ∀ K, F.mapDerivedCategory.map
        ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctorUnitQ K) ≫
        β.app (DerivedCategory.Q.obj K) ≫
        (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctor.map
          (((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapDerivedCategoryFactors.hom.app K) =
      F.mapDerivedCategoryFactors.hom.app
          (((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (preservesLimitNatIso (J := ℕᵒᵖ) F).hom (.up ℤ)).app K) ≫
        (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctorUnitQ ((roosTowerAction F).obj K))
    (K : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    F.mapDerivedCategory.map (κA.hom.app K) ≫ β.app (DerivedCategory.Q.obj K) =
      F.mapDerivedCategoryFactors.hom.app (roosF.obj K) ≫
        DerivedCategory.Q.map (roosAdditiveComparison F K) ≫
        κB.hom.app ((roosTowerAction F).obj K) ≫
        (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctor.map
          (((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapDerivedCategoryFactors.inv.app K) := by
  exact roos_normalized_square F κA κB hA hB β hn K

private theorem cochainUnit_eq
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions C] (G : C ⥤ D) [G.Additive]
    (K : CochainComplex C ℤ) :
    UnboundedExactTower.cochainUnit G K = G.rightDerivedFunctorUnitQ K := by
  unfold UnboundedExactTower.cochainUnit Functor.rightDerivedFunctorUnitQ
  simp only [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv]
  erw [(DerivedCategory.Qh (C := D)).map_id]
  repeat erw [Category.id_comp]

private theorem ordinaryMate
    {C D : Type*} [Category C] [Category D]
    [HasLimitsOfShape ℕᵒᵖ C] [HasLimitsOfShape ℕᵒᵖ D]
    (G : C ⥤ D) [PreservesLimitsOfShape ℕᵒᵖ G] :
    (mateEquiv (constLimAdj : (Functor.const ℕᵒᵖ : C ⥤ _) ⊣ lim)
      (constLimAdj : (Functor.const ℕᵒᵖ : D ⥤ _) ⊣ lim)
      (Functor.compConstIso ℕᵒᵖ G).hom).natTrans =
        (preservesLimitNatIso G (J := ℕᵒᵖ)).hom := by
  let aa := (constLimAdj : (Functor.const ℕᵒᵖ : C ⥤ _) ⊣ lim)
  let bb := (constLimAdj : (Functor.const ℕᵒᵖ : D ⥤ _) ⊣ lim)
  apply NatTrans.ext
  funext M
  apply limit.hom_ext
  intro n
  have h := congrArg (fun z ↦ z.app n)
    (mateEquiv_counit aa bb (Functor.compConstIso ℕᵒᵖ G).hom M)
  change (mateEquiv aa bb (Functor.compConstIso ℕᵒᵖ G).hom).natTrans.app M ≫
    limit.π _ n = 𝟙 _ ≫ G.map (limit.π M n) at h
  rw [Category.id_comp] at h
  exact h.trans (preservesLimitIso_hom_π G M n).symm

private theorem mate_unit_normalization
    (e : F.mapDerivedCategory ⋙ (Functor.const ℕᵒᵖ : B ⥤ _).mapDerivedCategory ≅
      (Functor.const ℕᵒᵖ : A ⥤ _).mapDerivedCategory ⋙ (towerF F).mapDerivedCategory)
    (he : UnboundedExactTower.localizedSquare
      (Functor.const ℕᵒᵖ) (Functor.const ℕᵒᵖ) F (towerF F)
        (Functor.compConstIso ℕᵒᵖ F) = e)
    (K : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    F.mapDerivedCategory.map
        ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctorUnitQ K) ≫
      (mateEquiv
        (constLimAdj : (Functor.const ℕᵒᵖ : A ⥤ _) ⊣ lim).mapDerivedCategoryRightDerivedAdjunction
        (constLimAdj : (Functor.const ℕᵒᵖ : B ⥤ _) ⊣ lim).mapDerivedCategoryRightDerivedAdjunction
        (TwoSquare.mk _ _ _ _ e.hom)).natTrans.app (DerivedCategory.Q.obj K) ≫
      (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctor.map
        ((towerF F).mapDerivedCategoryFactors.hom.app K) =
      F.mapDerivedCategoryFactors.hom.app
          (((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (preservesLimitNatIso (J := ℕᵒᵖ) F).hom (.up ℤ)).app K) ≫
        (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctorUnitQ ((roosTowerAction F).obj K) := by
  have h := UnboundedExactTower.localized_mate_cochain_normalization
    (constLimAdj : (Functor.const ℕᵒᵖ : A ⥤ _) ⊣ lim)
    (constLimAdj : (Functor.const ℕᵒᵖ : B ⥤ _) ⊣ lim)
    (Functor.compConstIso ℕᵒᵖ F) K
  rw [he] at h
  simp only [cochainUnit_eq, ordinaryMate] at h
  apply (cancel_epi (F.mapDerivedCategoryFactors.inv.app _)).mp
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  exact h

private theorem iso_chain
    {C D V W : Type*} [Category C] [Category D] [Category V] [Category W]
    (F : C ⥤ D) (Q : V ⥤ D) (R : W ⥤ D)
    {A A' : C} {B B' : V} {T T' : W}
    (a : A ≅ A') (b : F.obj A ≅ Q.obj B) (c : B ≅ B')
    (d : Q.obj B' ≅ R.obj T) (e : T ≅ T') (β : F.obj A' ⟶ R.obj T')
    (h : F.map a.hom ≫ β = b.hom ≫ Q.map c.hom ≫ d.hom ≫ R.map e.hom) :
    IsIso β ∧
      F.map a.inv ≫ b.hom ≫ Q.map c.hom ≫ d.hom ≫ R.map e.hom = β := by
  have he : F.map a.inv ≫ b.hom ≫ Q.map c.hom ≫ d.hom ≫ R.map e.hom = β := by
    rw [← h, ← F.map_comp_assoc, Iso.inv_hom_id, F.map_id, Category.id_comp]
  refine ⟨?_, he⟩
  rw [← he]
  infer_instance

private theorem iso_chain_of_eq
    {C D V W : Type*} [Category C] [Category D] [Category V] [Category W]
    (F : C ⥤ D) (Q : V ⥤ D) (R : W ⥤ D)
    {A A' : C} {B B' : V} {T T' : W}
    (a a' : A ≅ A') (ha : a = a') (b : F.obj A ≅ Q.obj B)
    (c : B ⟶ B') (c' : B ≅ B') (hc : c = c'.hom)
    (d d' : Q.obj B' ≅ R.obj T) (hd : d = d') (e : T ≅ T')
    (β β' : F.obj A' ⟶ R.obj T') (hβ : β = β')
    (h : F.map a.hom ≫ β = b.hom ≫ Q.map c ≫ d.hom ≫ R.map e.hom) :
    IsIso β' ∧
      F.map a'.inv ≫ b.hom ≫ Q.map c'.hom ≫ d'.hom ≫ R.map e.hom = β' := by
  subst a'
  subst d'
  subst β'
  rw [hc] at h
  exact iso_chain F Q R a b c' d e β h

private theorem comparison_hom_eq
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasCountableProducts C] [HasCountableProducts D] (G : C ⥤ D) [G.Additive]
    (M : CochainComplex (ℕᵒᵖ ⥤ C) ℤ)
    (q : (G.mapHomologicalComplex (.up ℤ)).obj (strictRoosProduct M) ⟶
      strictRoosProduct ((roosTowerAction G).obj M))
    (hq : q = roosProductComparison G M)
    (e : (G.mapHomologicalComplex (.up ℤ)).obj (strictRoosComplex M) ≅
      strictRoosComplex ((roosTowerAction G).obj M))
    (he : ∀ p : ℤ, e.hom.f (p + 1) ≫
        (strictRoosCoordinates ((roosTowerAction G).obj M) p).hom =
      G.map (strictRoosCoordinates M p).hom ≫ biprodComparison G _ _ ≫
        biprod.map (q.f p)
          (q.f (p + 1))) :
    e.hom = roosAdditiveComparison G M := by
  rw [hq] at he
  apply HomologicalComplex.Hom.ext
  funext k
  obtain ⟨p, rfl⟩ := (Equiv.addRight (1 : ℤ)).surjective k
  apply (cancel_mono (strictRoosCoordinates ((roosTowerAction G).obj M) p).hom).mp
  exact (he p).trans (roosAdditiveComparison_coordinates G M p).symm

private theorem normalized_family
    [IsGrothendieckAbelian.{v} (ℕᵒᵖ ⥤ A)]
    [HasExactLimitsOfShape (Discrete ℕ) A]
    (e : ∀ M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
      DerivedCategory.Q.obj (strictRoosComplex M) ≅
        (lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctor.obj (DerivedCategory.Q.obj M))
    (he : (∀ (M N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (a : M ⟶ N),
      DerivedCategory.Q.map (roosF.map a) ≫ (e N).hom =
        (e M).hom ≫ (lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctor.map
          (DerivedCategory.Q.map a)) ∧
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) [I.IsKInjective],
        DerivedCategory.Q.map (roosι I) ≫ (e I).hom =
          DerivedCategory.Q.map (ExactAdjointTowerModels.ordinaryIso.inv.app I) ≫
            ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctorObjQIso I).inv)) :
    ∃ κ : roosF (A := A) ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙
        (lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctor,
      (∀ M, κ.app M = e M) ∧
      (∀ M, DerivedCategory.Q.map (roosι M) ≫ κ.hom.app M =
        DerivedCategory.Q.map (ExactAdjointTowerModels.ordinaryIso.inv.app M) ≫
          (lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctorUnitQ M) := by
  obtain ⟨κ, hκ⟩ := normalized_roos_iso (A := A)
  refine ⟨κ, ?_, hκ⟩
  have h : (fun M ↦ κ.app M) = e := by
    apply (normalized_roos_iso_unique (A := A)).unique
    · refine ⟨fun _ _ a ↦ κ.hom.naturality a, ?_⟩
      intro I hI
      rw [← Functor.rightDerivedFunctorUnitQ_eq]
      exact hκ I
    · exact he
  exact fun M ↦ congrFun h M

private theorem roos_factorization
    (eA : ∀ K : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
      DerivedCategory.Q.obj (strictRoosComplex K) ≅
        (lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctor.obj (DerivedCategory.Q.obj K))
    (eB : ∀ K : CochainComplex (ℕᵒᵖ ⥤ B) ℤ,
      DerivedCategory.Q.obj (strictRoosComplex K) ≅
        (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctor.obj (DerivedCategory.Q.obj K))
    (hA : ∃ κ : roosF (A := A) ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙
        (lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctor,
      (∀ K, κ.app K = eA K) ∧
      (∀ K, DerivedCategory.Q.map (roosι K) ≫ κ.hom.app K =
        DerivedCategory.Q.map (ExactAdjointTowerModels.ordinaryIso.inv.app K) ≫
          (lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctorUnitQ K))
    (hB : ∃ κ : roosF (A := B) ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙
        (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctor,
      (∀ K, κ.app K = eB K) ∧
      (∀ K, DerivedCategory.Q.map (roosι K) ≫ κ.hom.app K =
        DerivedCategory.Q.map (ExactAdjointTowerModels.ordinaryIso.inv.app K) ≫
          (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctorUnitQ K))
    (β : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctor ⋙ F.mapDerivedCategory ⟶
      (towerF F).mapDerivedCategory ⋙ (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctor)
    (b : ∀ N, F.mapDerivedCategory.obj
        ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctor.obj N) ⟶
      (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctor.obj
        ((towerF F).mapDerivedCategory.obj N))
    (hb : ∀ N, β.app N = b N)
    (hn : ∀ K, F.mapDerivedCategory.map
        ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).rightDerivedFunctorUnitQ K) ≫
        β.app (DerivedCategory.Q.obj K) ≫
        (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctor.map
          ((towerF F).mapDerivedCategoryFactors.hom.app K) =
      F.mapDerivedCategoryFactors.hom.app
          (((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (preservesLimitNatIso (J := ℕᵒᵖ) F).hom (.up ℤ)).app K) ≫
        (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctorUnitQ ((roosTowerAction F).obj K))
    (K : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (e : (F.mapHomologicalComplex (.up ℤ)).obj (strictRoosComplex K) ≅
      strictRoosComplex ((roosTowerAction F).obj K))
    (he : e.hom = roosAdditiveComparison F K) :
    IsIso (b (DerivedCategory.Q.obj K)) ∧
      F.mapDerivedCategory.map (eA K).inv ≫
        F.mapDerivedCategoryFactors.hom.app (strictRoosComplex K) ≫
        DerivedCategory.Q.map e.hom ≫ (eB ((roosTowerAction F).obj K)).hom ≫
        (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctor.map
          ((towerF F).mapDerivedCategoryFactors.inv.app K) = b (DerivedCategory.Q.obj K) := by
  obtain ⟨κA, heA, hA⟩ := hA
  obtain ⟨κB, heB, hB⟩ := hB
  have hs := roos_normalized_square_ordinary F κA κB hA hB β hn K
  exact iso_chain_of_eq F.mapDerivedCategory DerivedCategory.Q
    (lim : (ℕᵒᵖ ⥤ B) ⥤ B).rightDerivedFunctor
    (κA.app K) (eA K) (heA K)
    (F.mapDerivedCategoryFactors.app (strictRoosComplex K))
    (roosAdditiveComparison F K) e he.symm
    (κB.app ((roosTowerAction F).obj K)) (eB ((roosTowerAction F).obj K))
    (heB ((roosTowerAction F).obj K)) ((towerF F).mapDerivedCategoryFactors.symm.app K)
    (β.app (DerivedCategory.Q.obj K)) (b (DerivedCategory.Q.obj K)) (hb _) hs

end ImmersionRoosMateProof

namespace AlgebraicGeometry.Scheme
namespace ImmersionCompletedPullback

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable {X Y : Scheme.{u}} (f : Y ⟶ X)

attribute [local irreducible] pbcIntegralDatum

/-- Identify the two strict constructions by their specified augmentation units.
Source: localization Step 6, Steps 2 and 5
(blueprint: lem-sf-immersion-completed-pullback-comparison).
Proof: apply moduleIso levelwise and derive its exact tower functor. The chosen
Rlim functors are the same universal right-derived limit. Their induced comparison
carries the quotient augmentation to itself, giving the displayed equation.
Completion is a reflector into complete objects, so its unit forces uniqueness. -/
theorem strictIso_exists :
    ∃! e : pbcActualStrictCompletedPull (pbcIntegralDatum l E) f ≅
        (pbcIntegralDatum l E).completedPull f,
      ∀ K : PbcCompletedDerived X (pbcIntegralDatum l E),
        (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) f).app K ≫ e.hom.app K =
          (derivedIso l E f).hom.app K ≫ (pbcIntegralDatum l E).ordinaryToCompleted f K := by
  let d := pbcIntegralDatum l E
  let e := cbcDatumActualStrictTransport d f
  have he (K : PbcCompletedDerived X d) :
      (pbcActualStrictCompletedPullUnit d f).app K ≫ e.hom.app K =
        (derivedIso l E f).hom.app K ≫ d.ordinaryToCompleted f K := by
    rw [← ordinary_transport_eq]
    exact cbcDatumActualStrictTransport_unit d f K
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext K
  obtain ⟨r, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp d.finitelyGenerated
  obtain ⟨α, hα⟩ := strict_completion l E f r a ha K
  have hcomplete := (wfCompletionReflector Y d r a ha).1
    ((pbcActualDerivedPull f d).obj K)
  have hsource : WfIsComplete Y d r a ha
      ((pbcActualStrictCompletedPull d f).obj K) :=
    (wfComplete_iso Y d r a ha α).mpr hcomplete
  have htarget := (wfComplete_iso Y d r a ha (e.app K)).mp hsource
  apply (cancel_epi α.inv).mp
  apply ((wfCompletionReflector Y d r a ha).2 _ _ htarget).injective
  rw [← hα]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact (he' K).trans (he K).symm


/-- The unit-normalized identification of the actual strict construction.
Source: localization Step 6, Step 5
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
def strictIso := (strictIso_exists l E f).exists.choose

/-- The finite projection of the actual completed pullback, with its finite comparison.
Source: localization Step 6, Step 5
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
def actualCompletedProjection
    (K : PbcCompletedDerived X (pbcIntegralDatum l E)) (n : ℕ) :
    (pbcActualStrictCompletedPull (pbcIntegralDatum l E) f).obj K ⟶
      (restrictedReduction l E Y n).obj
        ((pbcActualDerivedPull f (pbcIntegralDatum l E)).obj K) :=
  (strictIso l E f).hom.app K ≫ completedProjection l E f K n ≫
    (restrictedComparison l E f n).hom.app K ≫
    (restrictedReduction l E Y n).map ((derivedIso l E f).inv.app K)

private theorem scalarTransition_natural (T : Scheme.{u})
    {R S B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ B) (χ : R ⟶ B) (h : φ ≫ ψ = χ)
    {K L : DerivedCategory (pbcModules T R)} (a : K ⟶ L) :
    (pbcDerivedExtend φ).map a ≫ pbcReductionTransition φ ψ χ h L =
      pbcReductionTransition φ ψ χ h K ≫
        (pbcDerivedRestrict ψ).map ((pbcDerivedExtend χ).map a) := by
  let adj := pbcDerivedScalarAdjunction φ
  apply (adj.homEquiv K _).injective
  dsimp only [pbcReductionTransition]
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  simp only [Category.assoc]
  have hn := (pbcDerivedRestrictComp φ ψ χ h).inv.naturality
    ((pbcDerivedExtend χ).map a)
  dsimp only [Functor.comp_map] at hn
  have hu := (pbcDerivedScalarAdjunction χ).unit.naturality a
  dsimp only [Functor.id_map, Functor.comp_map] at hu
  rw [← hn, ← Category.assoc, hu, Category.assoc]

private theorem reductionTransition_natural (T : Scheme.{u})
    (b a : ℕ) (h : a ≤ b)
    {K L : PbcCompletedDerived T (pbcIntegralDatum l E)} (g : K ⟶ L) :
    (restrictedReduction l E T b).map g ≫ reductionTransition l E T b a h L =
      reductionTransition l E T b a h K ≫ (restrictedReduction l E T a).map g := by
  dsimp only [reductionTransition, restrictedReduction, Functor.comp_map]
  erw [← Category.assoc, ← Functor.map_comp,
    scalarTransition_natural, Functor.map_comp, Category.assoc]
  have hn := (pbcDerivedRestrictComp
    (pbcAdicProjection T (pbcIntegralDatum l E) b)
    (pbcAdicQuotient T (pbcIntegralDatum l E) b a h)
    (pbcAdicProjection T (pbcIntegralDatum l E) a)
    (pbcAdicProjection_comp T (pbcIntegralDatum l E) b a h)).hom.naturality
      ((pbcDerivedExtend (pbcAdicProjection T (pbcIntegralDatum l E) a)).map g)
  dsimp only [Functor.comp_map] at hn
  exact (congrArg (fun z ↦
    (pbcDerivedRestrict (pbcAdicProjection T (pbcIntegralDatum l E) b)).map
      (pbcReductionTransition (pbcAdicProjection T (pbcIntegralDatum l E) b)
        (pbcAdicQuotient T (pbcIntegralDatum l E) b a h)
        (pbcAdicProjection T (pbcIntegralDatum l E) a)
        (pbcAdicProjection_comp T (pbcIntegralDatum l E) b a h) K) ≫ z) hn).trans
      (Category.assoc _ _ _).symm

/-- The original strict comparison commutes with every actual finite projection.
Source: localization Step 6, Steps 2 and 5
(blueprint: lem-sf-immersion-completed-pullback-comparison).
Proof: combine the defining unit equation of strictIso with the unit square of
finite_compatibility and completedProjection_compatibility. Naturality of the
quotient units under derivedIso gives the first equality. The transition square
of finite_compatibility and naturality under the same isomorphism give the second,
for all quotients, including equal and successive indices. -/
theorem actualCompletedProjection_compatibility :
    (∀ (K : PbcCompletedDerived X (pbcIntegralDatum l E)) (n : ℕ),
      (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) f).app K ≫
          actualCompletedProjection l E f K n =
        (reductionUnit l E Y n).app
          ((pbcActualDerivedPull f (pbcIntegralDatum l E)).obj K)) ∧
    (∀ (K : PbcCompletedDerived X (pbcIntegralDatum l E)) (b a : ℕ) (h : a ≤ b),
      actualCompletedProjection l E f K b ≫ reductionTransition l E Y b a h
          ((pbcActualDerivedPull f (pbcIntegralDatum l E)).obj K) =
        actualCompletedProjection l E f K a) := by
  constructor
  · intro K n
    dsimp only [actualCompletedProjection]
    have hs := (strictIso_exists l E f).exists.choose_spec K
    change _ ≫ (strictIso l E f).hom.app K = _ at hs
    try simp only [Category.assoc]
    erw [reassoc_of% hs,
      reassoc_of% (completedProjection_compatibility l E f).1 K n,
      reassoc_of% (finite_compatibility l E f).1 K n]
    have hn := (reductionUnit l E Y n).naturality ((derivedIso l E f).inv.app K)
    dsimp only [Functor.id_map] at hn
    erw [← hn, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  · intro K b a h
    dsimp only [actualCompletedProjection]
    try simp only [Category.assoc]
    erw [reductionTransition_natural l E Y b a h ((derivedIso l E f).inv.app K),
      ← reassoc_of% (finite_compatibility l E f).2.1 K b a h,
      reassoc_of% (completedProjection_compatibility l E f).2 K b a h]

/-- The right mate of the identity-on-constant-towers inverse-image comparison.
Source: localization Step 6, Step 4
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
def rlimComparison
    (M : DerivedCategory (pbcTowers X (pbcAdicCompletion X (pbcIntegralDatum l E)))) :
    ((pbcIntegralDatum l E).pull f).obj
        ((completedRlim X ((pbcIntegralDatum l E).completedRing X)).obj M) ⟶
      (completedRlim Y ((pbcIntegralDatum l E).completedRing Y)).obj
        (((pbcIntegralDatum l E).towerPull f).obj M) :=
  ((pbcIntegralDatum l E).constantRlimAdjunction Y).unit.app _ ≫
    (completedRlim Y ((pbcIntegralDatum l E).completedRing Y)).map
      (((pbcIntegralDatum l E).derivedConstantPullbackIso f).inv.app _ ≫
        ((pbcIntegralDatum l E).towerPull f).map
          (((pbcIntegralDatum l E).constantRlimAdjunction X).counit.app M))

private theorem mate_augmentation
    {C D S U : Type*} [Category C] [Category D] [Category S] [Category U]
    (DX : C ⥤ S) (LX : S ⥤ C) (DY : D ⥤ U) (LY : U ⥤ D)
    (ax : DX ⊣ LX) (ay : DY ⊣ LY) (H : C ⥤ D) (T : S ⥤ U)
    (j : H ⋙ DY ⟶ DX ⋙ T) (K : C) (M : S) (i : DX.obj K ⟶ M) :
    ay.unit.app (H.obj K) ≫ LY.map (j.app K ≫ T.map i) =
      H.map (ax.unit.app K ≫ LX.map i) ≫
        (ay.unit.app (H.obj (LX.obj M)) ≫
          LY.map (j.app (LX.obj M) ≫ T.map (ax.counit.app M))) := by
  let h := ax.unit.app K ≫ LX.map i
  have hi : DX.map h ≫ ax.counit.app M = i := by
    dsimp only [h]
    rw [DX.map_comp, Category.assoc]
    have hn := ax.counit.naturality i
    dsimp only [Functor.comp_map, Functor.id_map] at hn
    rw [hn, ← Category.assoc]
    exact (congrArg (fun f ↦ f ≫ i) (ax.left_triangle_components K)).trans
      (Category.id_comp i)
  have hn := ay.unit.naturality (H.map h)
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  have hj := j.naturality h
  dsimp only [Functor.comp_map] at hj
  change _ = H.map h ≫ _
  symm
  rw [← Category.assoc, hn, Category.assoc, ← LY.map_comp]
  congr 1
  rw [← Category.assoc, hj, Category.assoc, ← T.map_comp, hi]
  rfl

/-- The canonical completion comparison factors through this actual Rlim mate.
Source: localization Step 6, Step 5
(blueprint: lem-sf-immersion-completed-pullback-comparison).
Proof: expand the two constant-tower adjunction units and apply the triangle
identity. Naturality with the quotient augmentation gives precisely this equation. -/
theorem ordinaryToCompleted_eq (K : PbcCompletedDerived X (pbcIntegralDatum l E)) :
    (pbcIntegralDatum l E).ordinaryToCompleted f K =
      ((pbcIntegralDatum l E).pull f).map ((pbcIntegralDatum l E).completionUnit X K) ≫
        rlimComparison l E f ((completedReductionTower X (pbcIntegralDatum l E)).obj K) := by
  exact mate_augmentation _ _ _ _
    ((pbcIntegralDatum l E).constantRlimAdjunction X)
    ((pbcIntegralDatum l E).constantRlimAdjunction Y)
    ((pbcIntegralDatum l E).pull f) ((pbcIntegralDatum l E).towerPull f)
    ((pbcIntegralDatum l E).derivedConstantPullbackIso f).inv K _
    ((completedReductionAugmentation (pbcIntegralDatum l E) X).app K)

/-- The ordinary module inverse image with canonical completed coefficients.
Source: localization Step 6, Step 1
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
abbrev modulePull :
    pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E)) ⥤
      pbcModules Y (pbcAdicCompletion Y (pbcIntegralDatum l E)) := proEtaleRingModulePullback f _ _
  ((pbcIntegralDatum l E).integralRingIso f)

/-- Apply the specified ordinary inverse image to all terms of a complex.
Source: localization Step 6, Step 1
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
abbrev complexPull := (modulePull l E f).mapHomologicalComplex (.up ℤ)

/-- Apply the same inverse image to every level and transition of a strict tower complex.
Source: localization Step 6, Steps 2 and 4
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
abbrev towerComplexPull :=
  ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (modulePull l E f)).mapHomologicalComplex (.up ℤ)

/-- Evaluation commutes with applying inverse image term by term.
Source: localization Step 6, Step 4
(blueprint: lem-sf-immersion-completed-pullback-comparison).
Proof: both complexes have inverse image of M_n in every degree and inverse image
of its differential; their chain maps and differential proofs agree by extensionality. -/
theorem complexEvaluation_eq
    (M : CochainComplex (pbcTowers X (pbcAdicCompletion X (pbcIntegralDatum l E))) ℤ)
    (n : ℕ) :
    (complexPull l E f).obj (M.asFunctor.obj (op n)) =
      ((towerComplexPull l E f).obj M).asFunctor.obj (op n) := by
  rfl

/-- The actual product comparison, determined by its projections.
Source: localization Step 6, Step 4
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
def productComparison
    (M : CochainComplex (pbcTowers X (pbcAdicCompletion X (pbcIntegralDatum l E))) ℤ) :
    (complexPull l E f).obj (strictRoosProduct M) ⟶
      strictRoosProduct ((towerComplexPull l E f).obj M) :=
  Pi.lift (f := fun n : ℕ ↦
    ((towerComplexPull l E f).obj M).asFunctor.obj (op n))
    (fun n : ℕ ↦ (complexPull l E f).map
    (Pi.π (fun k : ℕ ↦ M.asFunctor.obj (op k)) n) ≫
      eqToHom (complexEvaluation_eq l E f M n))

private theorem modulePull_preservesProducts [IsImmersion f] :
    PreservesLimitsOfShape (Discrete ℕ) (modulePull l E f) := by
  obtain ⟨_, _, _, _, _, _, h⟩ :=
    (proEtale_immersion_inverseImage_preservesLimits f).2.2
      ((pbcIntegralDatum l E).completedRing X)
  obtain ⟨P, hobj, hmap, _, _, _, hP⟩ :=
    h ((pbcIntegralDatum l E).completedRing Y) ((pbcIntegralDatum l E).integralRingIso f)
  have he : P = modulePull l E f := CategoryTheory.Functor.ext hobj hmap
  have : PreservesLimitsOfSize.{u + 1, u + 1} (modulePull l E f) := he ▸ hP
  have : PreservesLimitsOfSize.{0, 0} (modulePull l E f) :=
    preservesSmallestLimits_of_preservesLimits _
  infer_instance

/-- The coordinatewise Roos comparison, uniquely normalized by the product map.
Source: localization Step 6, Step 4; Stacks 08TC
(blueprint: lem-sf-immersion-completed-pullback-comparison).
Proof: inverse image preserves countable products for an immersion. Its product
comparison intertwines 1-s, since each projection gives the same pulled-back
transition. In the two Roos coordinates use this comparison on each factor.
The differentials (-dy-(1-s)x,dx) commute with this map; the inverse uses the
inverse product comparison. The coordinates jointly determine the chain map. -/
theorem roosIso_exists [IsImmersion f]
    (M : CochainComplex (pbcTowers X (pbcAdicCompletion X (pbcIntegralDatum l E))) ℤ) :
    ∃! e : (complexPull l E f).obj (strictRoosComplex M) ≅
        strictRoosComplex ((towerComplexPull l E f).obj M),
      ∀ p : ℤ, e.hom.f (p + 1) ≫
          (strictRoosCoordinates ((towerComplexPull l E f).obj M) p).hom =
        (modulePull l E f).map (strictRoosCoordinates M p).hom ≫
          biprodComparison (modulePull l E f) _ _ ≫
            biprod.map ((productComparison l E f M).f p)
              ((productComparison l E f M).f (p + 1)) := by
  have := modulePull_preservesProducts l E f
  have hpc : productComparison l E f M = roosProductComparison (modulePull l E f) M :=
    roos_product_comparison_formula (modulePull l E f) M (complexEvaluation_eq l E f M)
  rw [hpc]
  exact roos_iso_unique (modulePull l E f) M


/-- The strict Roos isomorphism; its data is fixed on both product coordinates.
Source: localization Step 6, Step 4
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
def roosIso [IsImmersion f]
    (M : CochainComplex (pbcTowers X (pbcAdicCompletion X (pbcIntegralDatum l E))) ℤ) :=
  (roosIso_exists l E f M).exists.choose

/-- A map of strict towers gives the uniquely coordinate-normalized Roos map.
Source: localization Step 6, Step 4; Stacks 08TC
(blueprint: lem-sf-immersion-completed-pullback-comparison).
Proof: naturality intertwines the two transition endomorphisms. Apply the shifted
mapping-cone construction; its two coordinates give the formula and uniqueness. -/
theorem roosMap_exists (T : Scheme.{u})
    {M N : CochainComplex (pbcTowers T (pbcAdicCompletion T (pbcIntegralDatum l E))) ℤ}
    (a : M ⟶ N) :
    ∃! b : strictRoosComplex M ⟶ strictRoosComplex N,
      ∀ p : ℤ, b.f (p + 1) ≫ (strictRoosCoordinates N p).hom =
        (strictRoosCoordinates M p).hom ≫
          biprod.map ((strictRoosProductMap a).f p) ((strictRoosProductMap a).f (p + 1)) := by
  refine ⟨roosF.map a, (fun p ↦ roosF_map_χ a p), ?_⟩
  intro b hb
  ext k : 1
  obtain ⟨p, rfl⟩ := (Equiv.addRight (1 : ℤ)).surjective k
  apply (cancel_mono (strictRoosCoordinates N p).hom).1
  exact (hb p).trans (roosF_map_χ a p).symm

/-- The strict map of the actual shifted Roos cones.
Source: localization Step 6, Step 4
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
def roosMap (T : Scheme.{u})
    {M N : CochainComplex (pbcTowers T (pbcAdicCompletion T (pbcIntegralDatum l E))) ℤ}
    (a : M ⟶ N) := (roosMap_exists l E T a).exists.choose

/-- The limit embeds into Roos by its zero and compatible-sequence coordinates.
Source: localization Step 6, Step 4; Stacks 07KC
(blueprint: lem-sf-immersion-completed-pullback-comparison).
Proof: a compatible sequence is killed by 1-s. Therefore these coordinates commute
with the displayed Roos differential; the coordinates also give uniqueness. -/
theorem roosInclusion_exists (T : Scheme.{u})
    (I : CochainComplex (pbcTowers T (pbcAdicCompletion T (pbcIntegralDatum l E))) ℤ) :
    ∃! a : limit I.asFunctor ⟶ strictRoosComplex I,
      ∀ p : ℤ, a.f (p + 1) ≫ (strictRoosCoordinates I p).hom =
        biprod.lift 0 ((Pi.lift (fun n : ℕ ↦ limit.π I.asFunctor (op n))).f (p + 1)) := by
  refine ⟨roosι I, (fun p ↦ roosι_χ I p), ?_⟩
  intro a ha
  ext k : 1
  obtain ⟨p, rfl⟩ := (Equiv.addRight (1 : ℤ)).surjective k
  apply (cancel_mono (strictRoosCoordinates I p).hom).1
  exact (ha p).trans (roosι_χ I p).symm

/-- The compatible-sequence inclusion, fixed on both cone coordinates.
Source: localization Step 6, Step 4
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
def roosInclusion (T : Scheme.{u})
    (I : CochainComplex (pbcTowers T (pbcAdicCompletion T (pbcIntegralDatum l E))) ℤ) :=
  (roosInclusion_exists l E T I).exists.choose

/-- The termwise limit and the limit of evaluated complexes have the same projections.
Source: localization Step 6, Step 4
(blueprint: lem-sf-immersion-completed-pullback-comparison).
Proof: limits of complexes are computed degreewise. Their universal property in
each degree gives this chain isomorphism and determines it by its projections. -/
theorem termwiseLimitIso_exists (T : Scheme.{u})
    (I : CochainComplex (pbcTowers T (pbcAdicCompletion T (pbcIntegralDatum l E))) ℤ) :
    ∃! e : (Functor.mapHomologicalComplex
        (completedTowerLimit T ((pbcIntegralDatum l E).completedRing T))
        (.up ℤ)).obj I ≅ limit I.asFunctor,
      ∀ (n : ℕ) (p : ℤ), e.hom.f p ≫ (limit.π I.asFunctor (op n)).f p =
        limit.π (I.X p) (op n) := by
  let c := HomologicalComplex.coneOfHasLimitEval I.asFunctor
  let hc := HomologicalComplex.isLimitConeOfHasLimitEval I.asFunctor
  let e := (limit.isoLimitCone ⟨c, hc⟩).symm
  have he (n : ℕ) (p : ℤ) :
      e.hom.f p ≫ (limit.π I.asFunctor (op n)).f p =
        limit.π (I.X p) (op n) := by
    exact congrArg (fun f ↦ HomologicalComplex.Hom.f f p)
      (limit.isoLimitCone_inv_π ⟨c, hc⟩ (op n))
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply limit.hom_ext
  intro n
  ext p : 1
  exact (he' n.unop p).trans (he n.unop p).symm

/-- The projection-normalized comparison of the two ordinary limit computations.
Source: localization Step 6, Step 4
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
def termwiseLimitIso (T : Scheme.{u})
    (I : CochainComplex (pbcTowers T (pbcAdicCompletion T (pbcIntegralDatum l E))) ℤ) :=
  (termwiseLimitIso_exists l E T I).exists.choose

private theorem roosMap_eq (T : Scheme.{u})
    {M N : CochainComplex (pbcTowers T (pbcAdicCompletion T (pbcIntegralDatum l E))) ℤ}
    (a : M ⟶ N) : roosMap l E T a = roosF.map a := by
  exact (roosMap_exists l E T a).unique
    (roosMap_exists l E T a).exists.choose_spec (fun p ↦ roosF_map_χ a p)

private theorem roosInclusion_eq (T : Scheme.{u})
    (I : CochainComplex (pbcTowers T (pbcAdicCompletion T (pbcIntegralDatum l E))) ℤ) :
    roosInclusion l E T I = roosι I := by
  exact (roosInclusion_exists l E T I).unique
    (roosInclusion_exists l E T I).exists.choose_spec (fun p ↦ roosι_χ I p)

private theorem termwiseLimitIso_eq (T : Scheme.{u})
    (I : CochainComplex (pbcTowers T (pbcAdicCompletion T (pbcIntegralDatum l E))) ℤ) :
    termwiseLimitIso l E T I = ExactAdjointTowerModels.ordinaryIso.app I := by
  apply (termwiseLimitIso_exists l E T I).unique
    (termwiseLimitIso_exists l E T I).exists.choose_spec
  intro n p
  exact ExactAdjointTowerModels.ordinaryIso_components I (op n) p

/-- Roos computes the recorded Rlim, naturally and with its universal derived unit.
Source: localization Step 6, Step 4; Stacks 07KC and 08TC
(blueprint: lem-sf-immersion-completed-pullback-comparison).
Proof: strictRoosDerivedLimitComparison makes the inclusion a quasi-isomorphism
on a K-injective tower. The universal derived unit identifies its ordinary limit
with Rlim. Every tower has a K-injective resolution; exact countable products make
Roos carry its quasi-isomorphism to a quasi-isomorphism. Descend the normalized
zigzag along that resolution. Naturality and the formula on K-injectives force
uniqueness, independently of the chosen resolution. -/
theorem roosRlim_exists (T : Scheme.{u}) :
    ∃! e : ∀ M : CochainComplex
        (pbcTowers T (pbcAdicCompletion T (pbcIntegralDatum l E))) ℤ,
        DerivedCategory.Q.obj (strictRoosComplex M) ≅
          (completedRlim T ((pbcIntegralDatum l E).completedRing T)).obj
            (DerivedCategory.Q.obj M),
      (∀ (M N : CochainComplex
          (pbcTowers T (pbcAdicCompletion T (pbcIntegralDatum l E))) ℤ) (a : M ⟶ N),
        DerivedCategory.Q.map (roosMap l E T a) ≫ (e N).hom =
          (e M).hom ≫ (completedRlim T ((pbcIntegralDatum l E).completedRing T)).map
            (DerivedCategory.Q.map a)) ∧
      (∀ (I : CochainComplex
          (pbcTowers T (pbcAdicCompletion T (pbcIntegralDatum l E))) ℤ) [I.IsKInjective],
        DerivedCategory.Q.map (roosInclusion l E T I) ≫ (e I).hom =
          DerivedCategory.Q.map (termwiseLimitIso l E T I).inv ≫
            (Functor.rightDerivedFunctorObjQIso
              (completedTowerLimit T ((pbcIntegralDatum l E).completedRing T)) I).inv) := by
  classical
  let R := pbcAdicCompletion T (pbcIntegralDatum l E)
  let A := pbcModules T R
  let : HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
    integralCoefficientAbSheafify.{u, 0} T
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    integralCoefficientAbLocallyBijective.{u, 0} T
  let : IsGrothendieckAbelian.{u + 1} (ℕᵒᵖ ⥤ A) :=
    reductionTower_isGrothendieckAbelian T (reductionModuleRing T R)
  let : HasExactLimitsOfShape (Discrete ℕ) A :=
    ProEt.products_exact.{u, u, 0} T (reductionModuleRing T R) ℕ
  simp only [roosMap_eq, roosInclusion_eq, termwiseLimitIso_eq]
  exact normalized_roos_iso_unique (A := A)

/-- The resolution-independent Roos identification fixed by the derived unit.
Source: localization Step 6, Step 4
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
def roosRlim (T : Scheme.{u}) := (roosRlim_exists l E T).exists.choose

private theorem roosRlim_normalized (T : Scheme.{u}) :
    ∃ κ : roosF (A := pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E))) ⋙
        DerivedCategory.Q ≅ DerivedCategory.Q ⋙ completedRlim T
          ((pbcIntegralDatum l E).completedRing T),
      (∀ M, κ.app M = roosRlim l E T M) ∧
      (∀ M, DerivedCategory.Q.map (roosι M) ≫ κ.hom.app M =
        DerivedCategory.Q.map (ExactAdjointTowerModels.ordinaryIso.inv.app M) ≫
          (completedTowerLimit T
            ((pbcIntegralDatum l E).completedRing T)).rightDerivedFunctorUnitQ M) := by
  let R := pbcAdicCompletion T (pbcIntegralDatum l E)
  let A := pbcModules T R
  let : HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
    integralCoefficientAbSheafify.{u, 0} T
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    integralCoefficientAbLocallyBijective.{u, 0} T
  let : IsGrothendieckAbelian.{u + 1} (ℕᵒᵖ ⥤ A) :=
    reductionTower_isGrothendieckAbelian T (reductionModuleRing T R)
  let : HasExactLimitsOfShape (Discrete ℕ) A :=
    ProEt.products_exact.{u, u, 0} T (reductionModuleRing T R) ℕ
  apply ImmersionRoosMateProof.normalized_family (roosRlim l E T)
  simpa only [roosRlim, roosMap_eq, roosInclusion_eq, termwiseLimitIso_eq,
    Iso.app_inv] using (roosRlim_exists l E T).exists.choose_spec

private theorem roosIso_hom_eq [IsImmersion f]
    (M : CochainComplex (pbcTowers X (pbcAdicCompletion X (pbcIntegralDatum l E))) ℤ) :
    (roosIso l E f M).hom = roosAdditiveComparison (modulePull l E f) M := by
  have hpc : productComparison l E f M = roosProductComparison (modulePull l E f) M :=
    roos_product_comparison_formula (modulePull l E f) M (complexEvaluation_eq l E f M)
  exact ImmersionRoosMateProof.comparison_hom_eq (modulePull l E f) M
    (productComparison l E f M) hpc (roosIso l E f M)
    (roosIso_exists l E f M).exists.choose_spec


private theorem constantRlimAdjunction_eq
    {R : Type (u + 1)} [CommRing R] (d : AdicCoefficientDatum R) (T : Scheme.{u}) :
    d.constantRlimAdjunction T =
      (constLimAdj : (Functor.const ℕᵒᵖ : reductionModules T (d.completedRing T) ⥤ _) ⊣
        lim).mapDerivedCategoryRightDerivedAdjunction := by
  rfl

/-- The actual right mate is the map induced on strict Roos coordinates.
Source: localization Step 6, Steps 4 and 5
(blueprint: lem-sf-immersion-completed-pullback-comparison).
Proof: on strict towers inverse image commutes with both Roos coordinates by
roosIso. Normalize Roos-to-Rlim by its K-injective inclusion and universal unit.
The constant-tower adjunction mate has exactly these normalized coordinates,
so naturality on resolutions gives the displayed equation. The product maps
are invertible for immersions, hence the mate is invertible as well. -/
theorem rlimComparison_roos [IsImmersion f]
    (M : CochainComplex (pbcTowers X (pbcAdicCompletion X (pbcIntegralDatum l E))) ℤ) :
    IsIso (rlimComparison l E f (DerivedCategory.Q.obj M)) ∧
      ((pbcIntegralDatum l E).pull f).map ((roosRlim l E X M).inv) ≫
          (modulePull l E f).mapDerivedCategoryFactors.hom.app (strictRoosComplex M) ≫
          DerivedCategory.Q.map (roosIso l E f M).hom ≫
          (roosRlim l E Y ((towerComplexPull l E f).obj M)).hom ≫
          (completedRlim Y ((pbcIntegralDatum l E).completedRing Y)).map
            (((pbcIntegralDatum l E).towerModulePull f).mapDerivedCategoryFactors.inv.app M) =
        rlimComparison l E f (DerivedCategory.Q.obj M) := by
  let F := modulePull l E f
  let W := (Functor.whiskeringRight ℕᵒᵖ _ _).obj F
  let d := pbcIntegralDatum l E
  let β := (mateEquiv
    (constLimAdj : (Functor.const ℕᵒᵖ : pbcModules X (pbcAdicCompletion X d) ⥤ _) ⊣
      lim).mapDerivedCategoryRightDerivedAdjunction
    (constLimAdj : (Functor.const ℕᵒᵖ : pbcModules Y (pbcAdicCompletion Y d) ⥤ _) ⊣
      lim).mapDerivedCategoryRightDerivedAdjunction
    (TwoSquare.mk _ _ _ _ (d.derivedConstantPullbackIso f).inv)).natTrans
  have hβ (N) : β.app N = rlimComparison l E f N := by
    as_aux_lemma =>
      simp only [rlimComparison, constantRlimAdjunction_eq]
      simp only [β, mateEquiv, Equiv.coe_fn_mk, TwoSquare.mk,
        NatTrans.comp_app, Functor.rightUnitor_inv_app, Functor.whiskerLeft_app,
        Functor.associator_hom_app, Functor.associator_inv_app, Functor.whiskerRight_app,
        Functor.comp_map, Functor.leftUnitor_hom_app, Category.id_comp, Category.comp_id,
        rlimComparison, Functor.map_comp, Functor.map_id, Category.assoc]
      dsimp only [TwoSquare.natTrans, Functor.comp_obj]
      dsimp only [d]
      simp only [Category.id_comp, Category.comp_id]
      erw [Category.comp_id]
  let : PreservesLimitsOfShape (Discrete ℕ) F := modulePull_preservesProducts l E f
  let : PreservesLimitsOfShape ℕᵒᵖ F := CategoryTheory.natProducts_preservesTowers F
  have hi : d.constantPullbackIso f = (Functor.compConstIso ℕᵒᵖ F).symm := by
    as_aux_lemma =>
      ext N n
      rfl
  have hsquare : UnboundedExactTower.localizedSquare
      (Functor.const ℕᵒᵖ) (Functor.const ℕᵒᵖ) F W
        (Functor.compConstIso ℕᵒᵖ F) = (d.derivedConstantPullbackIso f).symm := by
    as_aux_lemma =>
      exact constantDerivedSquare_eq F (d.constantPullbackIso f) hi
  exact ImmersionRoosMateProof.roos_factorization F (roosRlim l E X) (roosRlim l E Y)
    (roosRlim_normalized l E X) (roosRlim_normalized l E Y) β
    (fun N ↦ rlimComparison l E f N) hβ
    (fun K ↦ ImmersionRoosMateProof.mate_unit_normalization F
      (d.derivedConstantPullbackIso f).symm hsquare K) M
    (roosIso l E f M) (roosIso_hom_eq l E f M)


private theorem quotientEquiv_eq (n : ℕ) :
    quotientEquiv l E n = integralCoefficientULift l E n := by
  exact (quotientEquiv_exists l E n).unique
    (quotientEquiv_exists l E n).exists.choose_spec
    (integralCoefficientULift_exists l E n).exists.choose_spec

private theorem completedRingIso_eq (T : Scheme.{u}) :
    completedRingIso l E T = purCoefficientIso l E T := by
  apply (purCoefficientIso_existsUnique l E T).unique
  · apply (integralDetailedCoefficientComparison_exists T l E).unique
    · intro n
      have h := congrArg ((adicLisseForget T).map)
        ((completedRingIso_exists l E T).exists.choose_spec n)
      have hp : (adicLisseForget T).map
          (completedIntegralCommRingProjectionUnrestricted l E T n) =
          limit.π (integralCoefficientSheafSystem l E T) (op n) := by
        apply Sheaf.hom_ext
        ext U x
        rfl
      simpa only [Functor.map_comp, hp, Functor.mapIso_hom, completedRingIso,
        finiteRingIso, integralDetailedLevelComparison,
        quotientEquiv_eq l E] using h
    · exact (integralDetailedCoefficientComparison_exists T l E).exists.choose_spec
  · exact (purCoefficientIso_existsUnique l E T).exists.choose_spec

private theorem transport_complete_iff (T : Scheme.{u})
    (K : PbcCompletedDerived T (pbcIntegralDatum l E)) :
    PbcIsIntrinsicallyComplete T (pbcIntegralDatum l E) K ↔
      IntegralOnSlice.IsComplete l E T none ((transport l E T).obj K) := by
  have h := (purCoefficientModel_predicates l E T K).1
  simpa only [transport, completedRingIso_eq l E, purCoefficientModel,
    Equivalence.changeFunctor] using h

private theorem transport_sfComplete_iff (T : Scheme.{u})
    (K : PbcCompletedDerived T (pbcIntegralDatum l E)) :
    PbcIsIntrinsicallyComplete T (pbcIntegralDatum l E) K ↔
      IsSfDerivedComplete l E T ((transport l E T).obj K) := by
  have h := (purCoefficientModel_predicates l E T K).2
  simpa only [transport, completedRingIso_eq l E, purCoefficientModel,
    Equivalence.changeFunctor] using h

private theorem rlimComparison_isIso [IsImmersion f]
    (T : DerivedCategory (pbcTowers X (pbcAdicCompletion X (pbcIntegralDatum l E)))) :
    IsIso (rlimComparison l E f T) := by
  let d := pbcIntegralDatum l E
  let β := (mateEquiv (d.constantRlimAdjunction X) (d.constantRlimAdjunction Y)
    (TwoSquare.mk _ _ _ _ (d.derivedConstantPullbackIso f).inv)).natTrans
  have hβ (M) : β.app M = rlimComparison l E f M := by
    simp only [β, mateEquiv, Equiv.coe_fn_mk, TwoSquare.mk,
      NatTrans.comp_app, Functor.rightUnitor_inv_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Functor.whiskerRight_app,
      Functor.comp_map, Functor.leftUnitor_hom_app, Category.id_comp, Category.comp_id,
      rlimComparison, Functor.map_comp, Functor.map_id, Category.assoc]
    dsimp only [TwoSquare.natTrans, Functor.comp_obj]
    dsimp only [d]
    simp only [Category.id_comp, Category.comp_id]
    erw [Category.comp_id]
  let M := DerivedCategory.Q.objPreimage T
  let e : DerivedCategory.Q.obj M ≅ T := DerivedCategory.Q.objObjPreimageIso T
  have : IsIso (β.app (DerivedCategory.Q.obj M)) := by
    rw [hβ]
    exact (rlimComparison_roos l E f M).1
  have h := β.naturality e.hom
  have : IsIso ((completedRlim X (d.completedRing X) ⋙ d.pull f).map e.hom ≫ β.app T) := by
    rw [h]
    infer_instance
  rw [← hβ]
  exact IsIso.of_isIso_comp_left
    ((completedRlim X (d.completedRing X) ⋙ d.pull f).map e.hom) (β.app T)

private theorem actualStrictUnit_isIso [IsImmersion f]
    (K : PbcCompletedDerived X (pbcIntegralDatum l E))
    (hK : PbcIsIntrinsicallyComplete X (pbcIntegralDatum l E) K) :
    IsIso ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) f).app K) := by
  have hT := pbcIntrinsicComplete_towerComplete (pbcIntegralDatum l E) X K hK
  have : IsIso ((pbcIntegralDatum l E).completionUnit X K) := hT
  have := rlimComparison_isIso l E f
    ((completedReductionTower X (pbcIntegralDatum l E)).obj K)
  have : IsIso ((pbcIntegralDatum l E).ordinaryToCompleted f K) := by
    rw [ordinaryToCompleted_eq]
    infer_instance
  apply (isIso_comp_right_iff _ ((strictIso l E f).hom.app K)).mp
  change IsIso ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) f).app K ≫
    (strictIso_exists l E f).exists.choose.hom.app K)
  erw [(strictIso_exists l E f).exists.choose_spec K]
  infer_instance

private theorem ordinary_preservesIntrinsic [IsImmersion f]
    (K : PbcCompletedDerived X (pbcIntegralDatum l E))
    (hK : PbcIsIntrinsicallyComplete X (pbcIntegralDatum l E) K) :
    PbcIsIntrinsicallyComplete Y (pbcIntegralDatum l E)
      ((pbcActualDerivedPull f (pbcIntegralDatum l E)).obj K) := by
  have := actualStrictUnit_isIso l E f K hK
  let M : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete X
      (pbcIntegralDatum l E)) := ⟨K, hK⟩
  let e := (pbcActualCompletedPullback_tower (pbcIntegralDatum l E) f).exists.choose
  have he := (pbcActualCompletedPullback_tower (pbcIntegralDatum l E) f).exists.choose_spec M
  have : IsIso ((pbcActualCompletedPullUnit f (pbcIntegralDatum l E)).app K) := by
    rw [← he]
    infer_instance
  exact (actualComplete_iso Y (pbcIntegralDatum l E)
    (asIso ((pbcActualCompletedPullUnit f (pbcIntegralDatum l E)).app K))).mpr
    (pbcActualCompletedPull_isComplete f (pbcIntegralDatum l E) K)

private theorem immersion_completed_pullback_comparison_complete [IsImmersion f] :
    (∀ K : PbcCompletedDerived X (pbcIntegralDatum l E),
      IntegralOnSlice.IsComplete l E X none ((transport l E X).obj K) →
        (pbcIntegralDatum l E).TowerComplete X K ∧
        IsIso ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) f).app K) ∧
        IntegralOnSlice.IsComplete l E Y none
          ((transport l E Y).obj ((pbcActualDerivedPull f (pbcIntegralDatum l E)).obj K))) := by
  intro K hK
  have hX := (transport_complete_iff l E X K).mpr hK
  exact ⟨pbcIntrinsicComplete_towerComplete (pbcIntegralDatum l E) X K hX,
    actualStrictUnit_isIso l E f K hX,
    (transport_complete_iff l E Y _).mp (ordinary_preservesIntrinsic l E f K hX)⟩

private theorem immersion_completed_pullback_comparison_constructible [IsImmersion f] :
    ∀ (K : PbcCompletedDerived X (pbcIntegralDatum l E)) (r s : ℤ),
      r ≤ s → sfIntegralConstructible l E X ((transport l E X).obj K) →
      (∀ n : ℕ, proEtaleCohomologicalSupport
        ((scalarReductionDerivedExtension.{u, u} l E X n).obj
          ((transport l E X).obj K)) ⊆ Set.Icc r s) →
      sfIntegralConstructible l E Y
        ((transport l E Y).obj ((pbcActualDerivedPull f (pbcIntegralDatum l E)).obj K)) ∧
      ∀ n : ℕ, proEtaleCohomologicalSupport
        ((scalarReductionDerivedExtension.{u, u} l E Y n).obj
          ((transport l E Y).obj ((pbcActualDerivedPull f (pbcIntegralDatum l E)).obj K))) ⊆
            Set.Icc r s := by
  intro K r s hrs hK hb
  obtain ⟨hcomplete, a, b, hab, hfinite⟩ := hK
  have hX := (transport_sfComplete_iff l E X K).mpr hcomplete
  have hY := (transport_sfComplete_iff l E Y _).mp
    (ordinary_preservesIntrinsic l E f K hX)
  refine ⟨⟨hY, a, b, hab, ?_⟩, ?_⟩
  · intro n
    exact finite_reduction_preservesConstructibleInterval l E f K n a b (hfinite n)
  · intro n
    exact (finite_reduction_preservesConstructibleInterval l E f K n r s
      ⟨(hfinite n).1, hb n⟩).2

private theorem actualModulePull_finiteLimits [IsImmersion f] :
    PreservesFiniteLimits (pbcActualModulePull f (pbcIntegralDatum l E)) := by
  exact completedModulePullback_finiteLimits f (pbcIntegralDatum l E)

private theorem actualModulePull_finiteColimits [IsImmersion f] :
    PreservesFiniteColimits (pbcActualModulePull f (pbcIntegralDatum l E)) := by
  exact completedModulePullback_finiteColimits f (pbcIntegralDatum l E)

/-- Ordinary immersion inverse image is exact and preserves the specified complete
objects; the actual strict-tower unit is invertible on every derived-complete input.
The last clause uses the recorded integral category and keeps the given interval.
Source: localization Step 6; Stacks 09AA, 099M and 099N (2),(5)
(blueprint: lem-sf-immersion-completed-pullback-comparison).

Proof plan, following the node's Steps 1--6:
1. Identify completed and finite inverse-image coefficients by
   lem-weil-pbc-profinite-coefficient-inverse-image. Use
   lem-weil-pbc-proetale-immersion-limit-preservation for exactness and products;
   lem-sf-exact-functor-derived-triangulated identifies exact descent with Lu*.
2. Choose one flat-term K-flat representative. The canonical tensor-pullback
   comparisons of lem-weil-pbc-ringed-topoi-derived-tensor-pullback and
   lem-weil-pbc-ringed-topoi-module-pullback-tensor identify its strict quotient
   towers, including their augmentation and all quotient maps.
3. The finite-extension DVR gives the Noetherian adic datum (its quotients are
   finite and perfect). Use lem-weil-pbc-constant-completion-equivalence,
   lem-weil-pbc-ringed-koszul-completion-reflector and
   lem-weil-derived-limit-existence to show that the actual source completion
   unit, rather than an arbitrary isomorphism, is invertible. The signed
   Koszul-fibre-to-Roos identification carries the intrinsic unit to this unit.
4. Exact countable products (lem-weil-proetale-countable-products-exact) and
   lem-sf-strict-roos-derived-limit-comparison compute total inverse limit.
   Its inverse-image comparison is roosIso, with productComparison on both
   coordinates and the second coordinate as every finite projection.
5. The quotient augmentation is p mapped to (0,(p tensor 1)_n). Its image is
   the same augmentation for the pulled-back tower. Thus the specified strict
   completed-pullback comparison is the pullback of the source completion
   unit followed by this Roos comparison. All finite and successive quotient
   squares commute by finite_compatibility. This also gives completeness.
6. Use lem-sf-proetale-constructible-origin and
   lem-weil-pbc-pullback-preserves-bounded-constructible on every reduction.
   Each has exactly the original interval [r,s]. Together with completeness
   this is sfIntegralConstructible, with no additional boundedness condition. -/
theorem immersion_completed_pullback_comparison [IsImmersion f] :
    PreservesFiniteLimits (pbcActualModulePull f (pbcIntegralDatum l E)) ∧
    PreservesFiniteColimits (pbcActualModulePull f (pbcIntegralDatum l E)) ∧
    PreservesLimitsOfShape (Discrete ℕ) (modulePull l E f) ∧
    (∀ K : PbcCompletedDerived X (pbcIntegralDatum l E),
      IntegralOnSlice.IsComplete l E X none ((transport l E X).obj K) →
        (pbcIntegralDatum l E).TowerComplete X K ∧
        IsIso ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) f).app K) ∧
        IntegralOnSlice.IsComplete l E Y none
          ((transport l E Y).obj ((pbcActualDerivedPull f (pbcIntegralDatum l E)).obj K))) ∧
    (∀ (K : PbcCompletedDerived X (pbcIntegralDatum l E)) (r s : ℤ),
      r ≤ s → sfIntegralConstructible l E X ((transport l E X).obj K) →
      (∀ n : ℕ, proEtaleCohomologicalSupport
        ((scalarReductionDerivedExtension.{u, u} l E X n).obj
          ((transport l E X).obj K)) ⊆ Set.Icc r s) →
      sfIntegralConstructible l E Y
        ((transport l E Y).obj ((pbcActualDerivedPull f (pbcIntegralDatum l E)).obj K)) ∧
      ∀ n : ℕ, proEtaleCohomologicalSupport
        ((scalarReductionDerivedExtension.{u, u} l E Y n).obj
          ((transport l E Y).obj ((pbcActualDerivedPull f (pbcIntegralDatum l E)).obj K))) ⊆
            Set.Icc r s)   := by
  let hL := actualModulePull_finiteLimits l E f
  let hC := actualModulePull_finiteColimits l E f
  refine ⟨hL, hC, modulePull_preservesProducts l E f,
    immersion_completed_pullback_comparison_complete l E f,
    immersion_completed_pullback_comparison_constructible l E f⟩

end ImmersionCompletedPullback
end AlgebraicGeometry.Scheme

end NormalizationProofs
