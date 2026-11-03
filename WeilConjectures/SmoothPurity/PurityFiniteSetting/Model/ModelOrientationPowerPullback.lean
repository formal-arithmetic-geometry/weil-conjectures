/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.CompositionModelOrientationDefinitions
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackNormalization
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
import WeilConjectures.AlgebraicGeometry.Relative.RelativeKummerExchangeGeneratorsSupplement
import WeilConjectures.AlgebraicGeometry.Etale.EtaleSinglePullbackComparisonsSupplement
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackBase
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
import WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
import WeilConjectures.CategoryTheory.IntTensorFamilyIso
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
import Mathlib.CategoryTheory.Abelian.Refinements
import Mathlib.Algebra.Homology.ShortComplex.Exact
import WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.Defs.Filter
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.SixFunctors.Etale.Derived.Shift
import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
import Mathlib.Logic.Small.Defs
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteConstantUnitSquare
import WeilConjectures.AlgebraicGeometry.EtaleSectionUnitNormalization
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
import WeilConjectures.AlgebraicGeometry.ProjectiveLineDiagonalMaps
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedCartierKummerSupplement
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.AlgebraicGeometry.EtaleDiagonalSectionCoherence
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTraceCounit
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Data
import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat
import WeilConjectures.CategoryTheory.SectionConjugateComparison
import WeilConjectures.CategoryTheory.Adjunction.SmoothPurity.SectionProjectionUnitSupplement
import WeilConjectures.AlgebraicGeometry.EtaleTensorTraceBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided
import WeilConjectures.AlgebraicGeometry.EtaleCanonicalTensorComparison
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategorySymmetric
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Reduction
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionMonoidal
import WeilConjectures.CategoryTheory.DerivedSingleUnit
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackComparison
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteConstantPullbackHom
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackHom
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Vector.VectorPurityDirectSum
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Dnc.ComparisonPullbackDerivedCoherence
import WeilConjectures.AlgebraicGeometry.Ordered.OrderedTateCoefficientComposition
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Dnc.PurityDncInvariance
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.PurityCompositionCompatibleDncCharts
import all Mathlib.CategoryTheory.Limits.HasLimits
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonOpenTensorCoherence
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Pullback of ordered orientation powers -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

attribute [local instance] coefficientNoetherian

set_option maxHeartbeats 2000000 in
-- The coherence calculation elaborates large tensor and comparison expressions.
set_option maxHeartbeats 2000000 in
-- The coherence calculation elaborates large tensor and comparison expressions.
set_option maxHeartbeats 2000000 in
-- The coherence calculation elaborates large tensor and comparison expressions.
set_option maxHeartbeats 2000000 in
-- The coherence calculation elaborates large tensor and comparison expressions.
set_option maxHeartbeats 2000000 in
-- The coherence calculation elaborates large tensor and comparison expressions.
set_option maxHeartbeats 2000000 in
-- The coherence calculation elaborates large tensor and comparison expressions.

private theorem tensor_step {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.OplaxMonoidal]
    {X A B L : C} {X' A' B' L' : D}
    (a : X ≅ A ⊗ B) (a' : X' ≅ A' ⊗ B')
    (bX : F.obj X ⟶ X') (bA : F.obj A ⟶ A')
    (bB : F.obj B ⟶ B') (bL : F.obj L ⟶ L')
    (h : F.map a.hom ≫ Functor.OplaxMonoidal.δ F A B ≫ (bA ⊗ₘ bB) = bX ≫ a'.hom) :
    F.map ((a.hom ⊗ₘ 𝟙 L) ≫ (α_ A B L).hom) ≫
        Functor.OplaxMonoidal.δ F A (B ⊗ L) ≫
        (bA ⊗ₘ (Functor.OplaxMonoidal.δ F B L ≫ (bB ⊗ₘ bL))) =
      Functor.OplaxMonoidal.δ F X L ≫ (bX ⊗ₘ bL) ≫
        (a'.hom ⊗ₘ 𝟙 L') ≫ (α_ A' B' L').hom := by
  calc
    _ = F.map (a.hom ⊗ₘ 𝟙 L) ≫ F.map (α_ A B L).hom ≫
        Functor.OplaxMonoidal.δ F A (B ⊗ L) ≫
        (𝟙 (F.obj A) ⊗ₘ Functor.OplaxMonoidal.δ F B L) ≫
        (bA ⊗ₘ (bB ⊗ₘ bL)) := by
      simp only [CategoryTheory.Functor.map_comp, Category.assoc, tensorHom_comp_tensorHom,
        Category.id_comp]
    _ = F.map (a.hom ⊗ₘ 𝟙 L) ≫ Functor.OplaxMonoidal.δ F (A ⊗ B) L ≫
        (Functor.OplaxMonoidal.δ F A B ⊗ₘ 𝟙 (F.obj L)) ≫
        (α_ (F.obj A) (F.obj B) (F.obj L)).hom ≫ (bA ⊗ₘ (bB ⊗ₘ bL)) := by
      simp only [id_tensorHom, tensorHom_id]
      rw [← Functor.OplaxMonoidal.associativity_assoc]
    _ = Functor.OplaxMonoidal.δ F X L ≫
        (F.map a.hom ⊗ₘ 𝟙 (F.obj L)) ≫
        (Functor.OplaxMonoidal.δ F A B ⊗ₘ 𝟙 (F.obj L)) ≫
        ((bA ⊗ₘ bB) ⊗ₘ bL) ≫ (α_ A' B' L').hom := by
      rw [← Functor.OplaxMonoidal.δ_natural_assoc]
      simp only [CategoryTheory.Functor.map_id]
      rw [← associator_naturality]
    _ = Functor.OplaxMonoidal.δ F X L ≫
        ((F.map a.hom ≫ Functor.OplaxMonoidal.δ F A B ≫ (bA ⊗ₘ bB)) ⊗ₘ bL) ≫
        (α_ A' B' L').hom := by
      simp only [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]
    _ = _ := by
      rw [h]
      simp only [← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id]

private theorem power_add_eq (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (X : Scheme.{u}) (d e : ℕ) :
    compositionEtalePowerAdd A N hA X d e = purityPowerAdd A N hA X d e := by
  induction e with
  | zero =>
    apply Iso.ext
    simp only [compositionEtalePowerAdd, compositionEtalePowerAssembly,
      compositionOrderedPowerAdd, purityPowerAdd, Iso.trans_hom, Iso.symm_hom,
      Iso.trans_inv, Functor.mapIso_inv, eqToIso_refl, Iso.refl_trans,
      smoothPurityUnitIso, Etale.derivedTensorRightUnitor_eq, tensorIso_hom,
      Iso.refl_hom, Iso.symm_hom, id_tensorHom]
    rfl
  | succ e ih =>
    have hh := congrArg Iso.hom ih
    apply Iso.ext
    simp only [compositionEtalePowerAdd, compositionEtalePowerAssembly,
      compositionOrderedPowerAdd, eqToIso_refl, Iso.refl_trans,
      compositionTensorMapIso, Etale.derivedTensorAssociator_eq,
      Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
      Iso.refl_hom, CategoryTheory.Functor.map_id, Category.comp_id,
      purityPowerAdd] at hh ⊢
    rw [hh]
    simp only [Iso.symm_hom, Iso.refl_inv, tensorIso_hom, Iso.refl_hom]
    erw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
    simp only [MonoidalCategory.tensorHom_def, whiskerLeft_id, Category.comp_id]
    rfl

private theorem power_pullback (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (t : Etale.OrdinaryFiniteTwistTransport A N hA)
    {X Y : Scheme.{u}} (j : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤))) (d e : ℕ) :
    (Etale.ordinaryFinitePullback A j).mapIso (compositionEtalePowerAdd A N hA Y d e) ≪≫
      Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) j _ _ ≪≫
      Etale.ordinaryFiniteTensorRightMapIso A X
        (Etale.vectorIntegrationBaseCoefficientPullback A N hA t j hY d)
        (Etale.vectorIntegrationBaseCoefficientPullback A N hA t j hY e) =
    Etale.vectorIntegrationBaseCoefficientPullback A N hA t j hY (d + e) ≪≫
      compositionEtalePowerAdd A N hA X d e := by
  rw [power_add_eq, power_add_eq]
  let F := Etale.ordinaryFinitePullback A j
  let : F.OplaxMonoidal := Etale.leftDerivedUpperStarOplaxMonoidal (ModuleCat.{u + 1} A) j
  have tensor_map {K L K' L' : Etale.DerivedCategoryModule A X}
      (a : K ≅ K') (b : L ≅ L') :
      (Etale.ordinaryFiniteTensorRightMapIso A X a b).hom = a.hom ⊗ₘ b.hom := by
    change a.hom ▷ L ≫ K' ◁ b.hom = _
    rw [MonoidalCategory.tensorHom_def]
  have hη : Functor.OplaxMonoidal.η F =
      (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) j).hom := by
    exact Etale.leftDerivedUpperStarOplaxMonoidal_η (ModuleCat.{u + 1} A) j
  have tensor_pull (K L : Etale.DerivedCategoryModule A Y) :
      (Etale.ordinaryFiniteTensorPullback A j K L).hom =
        Functor.OplaxMonoidal.δ F K L := by rfl
  induction e with
  | zero =>
    apply Iso.ext
    have hzero := tensor_zero F
        (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} A) Y)
        (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} A) X)
        (Etale.vectorIntegrationBaseCoefficientPullback A N hA t j hY d).hom
        (Etale.ordinaryFiniteUnitPullback A j).hom
        (by rw [hη]
            exact Etale.ordinaryFiniteUnitPullback_hom_unit A j)
    simp only [purityPowerAdd, Iso.trans_hom, Functor.mapIso_hom,
      tensor_map, tensorIso_hom, Iso.refl_hom, Iso.symm_hom,
      Etale.vectorIntegrationBaseCoefficientPullback, Nat.add_zero] at hzero ⊢
    convert hzero using 1 <;> rfl
  | succ e ih =>
    apply Iso.ext
    have hh := congrArg Iso.hom ih
    simp only [Iso.trans_hom, Functor.mapIso_hom, tensor_map] at hh
    have hstep := tensor_step F (purityPowerAdd A N hA Y d e) (purityPowerAdd A N hA X d e)
        (Etale.vectorIntegrationBaseCoefficientPullback A N hA t j hY (d + e)).hom
        (Etale.vectorIntegrationBaseCoefficientPullback A N hA t j hY d).hom
        (Etale.vectorIntegrationBaseCoefficientPullback A N hA t j hY e).hom
        (Etale.ordinaryFiniteShiftedLinePullback A N hA t j hY).hom hh
    simp only [purityPowerAdd, Iso.trans_hom, Functor.mapIso_hom,
      tensor_map, tensorIso_hom, Iso.refl_hom, Nat.add_succ,
      Etale.vectorIntegrationBaseCoefficientPullback,
      tensor_pull, F, Nat.add_zero, Category.assoc] at hstep ⊢
    convert hstep using 1 <;> rfl

private theorem tate_comp (P : PurityFiniteSetting.{u})
    {T S R : Scheme.{u}} (a : T ⟶ S) (b : S ⟶ R)
    (aR : R ⟶ Spec (.of P.field.k)) (aS : S ⟶ Spec (.of P.field.k)) (d : ℕ) :
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) a).leftDerivedFunctor.mapIso
        (P.modelOrientationTwistPullback b aR d) ≪≫ P.modelOrientationTwistPullback a aS d =
      (ProEtale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) a b).symm.app
          (P.diagonalTwist R d) ≪≫ P.modelOrientationTwistPullback (a ≫ b) aR d := by
  let tw := Etale.projectiveLineTraceTransport P.diagonalExponent
    (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient P.diagonalExponent_annihilates
  let cb := Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient
    P.diagonalExponent P.diagonalExponent_annihilates tw b (P.diagonalExponent_isUnit aR) d
  have hn := congrArg Iso.hom (Dnc.pullComparison_naturality P a cb)
  have hc := Dnc.pullComparison_comp P a b (P.diagonalTwistEtale R d)
  have ht := Etale.orderedTateCoefficientComposition P.Coefficient P.diagonalExponent
    P.diagonalExponent_annihilates tw a b (a ≫ b) rfl
    (P.diagonalExponent_isUnit aR) (P.diagonalExponent_isUnit aS) d
  apply Iso.ext
  apply (cancel_epi ((ProEtale.leftDerivedUpperStarComp
    (ModuleCat.{u + 1} P.Coefficient) a b).hom.app (P.diagonalTwist R d))).mp
  simp only [modelOrientationTwistPullback, Functor.mapIso_trans, Iso.trans_hom,
    Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_app_assoc]
  simp only [Iso.trans_hom, Functor.mapIso_hom] at hn
  erw [reassoc_of% hn]
  erw [← reassoc_of% hc]
  simp only [← CategoryTheory.Functor.map_comp]
  exact congrArg (fun z ↦ (Dnc.pullComparison P (a ≫ b)
    (P.diagonalTwistEtale R d)).hom ≫
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory.map z) ht

set_option maxHeartbeats 2000000 in
-- The coherence calculation elaborates large tensor and comparison expressions.
private theorem tate_congr (P : PurityFiniteSetting.{u})
    {T S : Scheme.{u}} {a b : T ⟶ S} (h : a = b)
    (aS : S ⟶ Spec (.of P.field.k)) (d : ℕ) :
    (ProEtale.leftDerivedUpperStarCongr (ModuleCat.{u + 1} P.Coefficient) h).app
        (P.diagonalTwist S d) ≪≫ P.modelOrientationTwistPullback b aS d =
      P.modelOrientationTwistPullback a aS d := by
  subst b
  apply Iso.ext
  simp only [ProEtale.leftDerivedUpperStarCongr_rfl, Iso.trans_hom, Iso.app_hom,
    Iso.refl_hom, NatTrans.id_app, Category.id_comp]

set_option maxHeartbeats 2000000 in
-- The coherence calculation elaborates large tensor and comparison expressions.
set_option maxHeartbeats 2000000 in
-- The coherence calculation elaborates large tensor and comparison expressions.
end WeilConjectures.PurityFiniteSetting
