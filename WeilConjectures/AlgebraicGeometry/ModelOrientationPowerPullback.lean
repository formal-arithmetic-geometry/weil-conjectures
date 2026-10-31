/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompositionModelOrientationDefinitions
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackNormalization
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1KummerSupplement
import WeilConjectures.AlgebraicGeometry.RelativeKummerExchangeGeneratorsSupplement
import WeilConjectures.AlgebraicGeometry.EtaleSinglePullbackComparisonsSupplement
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
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedTensorPullback
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
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
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
import WeilConjectures.AlgebraicGeometry.EtaleDerivedTensorSymmetrySupplement
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
import WeilConjectures.AlgebraicGeometry.OrdinarySupportedCartierKummerSupplement
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.AlgebraicGeometry.EtaleDiagonalSectionCoherence
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTraceCounit
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Data
import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat
import WeilConjectures.CategoryTheory.SectionConjugateComparison
import WeilConjectures.CategoryTheory.SectionProjectionUnitSupplement
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
import WeilConjectures.AlgebraicGeometry.VectorPurityDirectSum
import WeilConjectures.AlgebraicGeometry.ComparisonPullbackDerivedCoherence
import WeilConjectures.AlgebraicGeometry.OrderedTateCoefficientComposition
import WeilConjectures.AlgebraicGeometry.ComparisonTensorPullback
import all WeilConjectures.AlgebraicGeometry.PurityCompositionCompatibleDncCharts
import all Mathlib.CategoryTheory.Limits.HasLimits

/-! # Pullback of ordered orientation powers -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

private theorem coefficientNoetherian (P : PurityFiniteSetting.{u}) :
    IsNoetherianRing P.Coefficient := isNoetherian_of_finite _ _
attribute [local instance] coefficientNoetherian

private theorem paste_iso_squares {C : Type*} [Category C]
    {A B C₁ D E F G Z : C}
    (a : A ≅ B) (b : B ≅ C₁) (c : C₁ ≅ Z)
    (d : B ≅ D) (e : D ≅ E) (p : E ≅ Z)
    (f : A ≅ F) (g : F ≅ D) (r : F ≅ G) (s : G ≅ E)
    (hp : b ≪≫ c = d ≪≫ e ≪≫ p)
    (hn : a ≪≫ d = f ≪≫ g) (hf : g ≪≫ e = r ≪≫ s) :
    a ≪≫ b ≪≫ c = f ≪≫ r ≪≫ s ≪≫ p := by
  rw [hp]
  rw [← Iso.trans_assoc a d, hn]
  simp only [Iso.trans_assoc]
  rw [← Iso.trans_assoc g e, hf]
  simp only [Iso.trans_assoc]

private theorem tensor_square_right {C D : Type*} [Category C] [Category D]
    (T : C ⥤ C ⥤ D) {K K' L M N M' : C} (a : K ≅ K')
    (b : L ≅ M) (c : M ≅ N) (b' : L ≅ M') (c' : M' ≅ N)
    (h : b ≪≫ c = b' ≪≫ c') :
    compatibleBifunctorIso T (Iso.refl K) b ≪≫ compatibleBifunctorIso T a c =
      compatibleBifunctorIso T a b' ≪≫ compatibleBifunctorIso T (Iso.refl K') c' := by
  rw [compatibleBifunctorIso_trans, compatibleBifunctorIso_trans]
  simp only [Iso.refl_trans, Iso.trans_refl, h]

set_option maxHeartbeats 2000000 in
-- The coherence calculation elaborates large tensor and comparison expressions.
private theorem tensor_zero {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.OplaxMonoidal]
    {A I : C} {A' I' : D} (z : I ≅ 𝟙_ C) (z' : I' ≅ 𝟙_ D)
    (bA : F.obj A ⟶ A') (bI : F.obj I ⟶ I')
    (h : bI ≫ z'.hom = F.map z.hom ≫ Functor.OplaxMonoidal.η F) :
    F.map ((ρ_ A).inv ≫ (𝟙 A ⊗ₘ z.inv)) ≫
        Functor.OplaxMonoidal.δ F A I ≫ (bA ⊗ₘ bI) =
      bA ≫ (ρ_ A').inv ≫ (𝟙 A' ⊗ₘ z'.inv) := by
  apply (cancel_mono ((𝟙 A' ⊗ₘ z'.hom) ≫ (ρ_ A').hom)).mp
  simp only [Category.assoc, tensorHom_comp_tensorHom_assoc, Category.comp_id,
    Iso.inv_hom_id, tensorHom_id, id_whiskerRight, Category.id_comp]
  calc
    _ = F.map (ρ_ A).inv ≫ F.map (𝟙 A ⊗ₘ z.inv) ≫
        Functor.OplaxMonoidal.δ F A I ≫
        (bA ⊗ₘ (F.map z.hom ≫ Functor.OplaxMonoidal.η F)) ≫ (ρ_ A').hom := by
      rw [h]
      simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    _ = F.map (ρ_ A).inv ≫ Functor.OplaxMonoidal.δ F A (𝟙_ C) ≫
        (bA ⊗ₘ Functor.OplaxMonoidal.η F) ≫ (ρ_ A').hom := by
      rw [← Functor.OplaxMonoidal.δ_natural_assoc]
      simp only [tensorHom_comp_tensorHom_assoc]
      rw [CategoryTheory.Functor.map_id, Category.id_comp, ← CategoryTheory.Functor.map_comp_assoc,
        Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
    _ = F.map (ρ_ A).inv ≫ Functor.OplaxMonoidal.δ F A (𝟙_ C) ≫
        (𝟙 (F.obj A) ⊗ₘ Functor.OplaxMonoidal.η F) ≫
        (ρ_ (F.obj A)).hom ≫ bA := by
      rw [← rightUnitor_naturality]
      simp only [← tensorHom_id, tensorHom_comp_tensorHom_assoc,
        Category.id_comp, Category.comp_id]
    _ = bA := by
      rw [id_tensorHom, Functor.OplaxMonoidal.right_unitality_hom_assoc]
      rw [← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id,
        CategoryTheory.Functor.map_id, Category.id_comp]

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

set_option maxHeartbeats 2000000 in
-- The coherence calculation elaborates large tensor and comparison expressions.
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

set_option maxHeartbeats 2000000 in
-- The coherence calculation elaborates large tensor and comparison expressions.
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

set_option maxHeartbeats 2000000 in
-- The coherence calculation elaborates large tensor and comparison expressions.
private theorem power_mul_pullback (P : PurityFiniteSetting.{u})
    {B' B : Scheme.{u}} (d e : ℕ) (b : B' ⟶ B)
    (aB : B ⟶ Spec (.of P.field.k)) :
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.mapIso
        (P.modelOrientationPowerMul B d e) ≪≫
      P.modelOrientationTwistPullback b aB (d + e) =
    ProEtale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} P.Coefficient) b
        (P.diagonalTwist B d) (P.diagonalTwist B e) ≪≫
      P.compatibleTensorIso (P.modelOrientationTwistPullback b aB d)
        (P.modelOrientationTwistPullback b aB e) ≪≫
      P.modelOrientationPowerMul B' d e := by
  let A := ModuleCat.{u + 1} P.Coefficient
  let F := (ProEtale.comparisonUpperStar A B).mapDerivedCategory
  let F' := (ProEtale.comparisonUpperStar A B').mapDerivedCategory
  let G := (Etale.upperStar A b).leftDerivedFunctor
  let H := (ProEtale.upperStar A b).leftDerivedFunctor
  let K := P.diagonalTwistEtale B d
  let L := P.diagonalTwistEtale B e
  let M := P.diagonalTwistEtale B (d + e)
  let K' := P.diagonalTwistEtale B' d
  let L' := P.diagonalTwistEtale B' e
  let M' := P.diagonalTwistEtale B' (d + e)
  let v := (compositionEtalePowerAdd P.Coefficient P.diagonalExponent
    P.diagonalExponent_annihilates B d e).symm
  let v' := (compositionEtalePowerAdd P.Coefficient P.diagonalExponent
    P.diagonalExponent_annihilates B' d e).symm
  let tw := Etale.projectiveLineTraceTransport P.diagonalExponent
    (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient P.diagonalExponent_annihilates
  let cd := Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient
    P.diagonalExponent P.diagonalExponent_annihilates tw b (P.diagonalExponent_isUnit aB) d
  let ce := Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient
    P.diagonalExponent P.diagonalExponent_annihilates tw b (P.diagonalExponent_isUnit aB) e
  let cm := Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient
    P.diagonalExponent P.diagonalExponent_annihilates tw b (P.diagonalExponent_isUnit aB)
    (d + e)
  let m := compatibleComparisonTensorGeneric A B K L
  let m' := compatibleComparisonTensorGeneric A B' (G.obj K) (G.obj L)
  let m'' := compatibleComparisonTensorGeneric A B' K' L'
  change H.mapIso (m.symm ≪≫ F.mapIso v) ≪≫
      (Dnc.pullComparison P b M ≪≫ F'.mapIso cm) =
    ProEtale.leftDerivedUpperStarTensorIso A b (F.obj K) (F.obj L) ≪≫
      compatibleBifunctorIso (ProEtale.derivedTensor A B')
        (Dnc.pullComparison P b K ≪≫ F'.mapIso cd)
        (Dnc.pullComparison P b L ≪≫ F'.mapIso ce) ≪≫ (m''.symm ≪≫ F'.mapIso v')
  let eta : F ⋙ H ≅ G ⋙ F' :=
    Functor.isoWhiskerLeft F (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory A b) ≪≫
      ProEtale.mapDerivedCategoryComparisonUpperStarCompUpperStarIso A b ≪≫
        Functor.isoWhiskerRight (Etale.leftDerivedUpperStarIsoMapDerivedCategory A b).symm F'
  have hn : H.mapIso (F.mapIso v) ≪≫ Dnc.pullComparison P b M =
      Dnc.pullComparison P b (((Etale.derivedTensor A B).obj K).obj L) ≪≫
        F'.mapIso (G.mapIso v) := by
    apply Iso.ext
    exact eta.hom.naturality v.hom
  have hc := comparisonTensorPullback P b K L
  have he : G.mapIso v ≪≫ cm =
      Etale.leftDerivedUpperStarTensorIso A b K L ≪≫
        compatibleBifunctorIso (Etale.derivedTensor A B') cd ce ≪≫ v' := by
      have hp := power_pullback P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates tw b (P.diagonalExponent_isUnit aB) d e
      apply Iso.ext
      have hh := congrArg Iso.hom hp
      simp only [Iso.trans_hom, Functor.mapIso_hom] at hh
      apply (cancel_mono v'.inv).mp
      simp only [Iso.trans_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]
      dsimp only [G, A, K, L, v, v', cm, diagonalTwistEtale,
        Etale.ordinaryFinitePullback] at hh ⊢
      simp only [Iso.symm_inv, Functor.mapIso_hom, Iso.symm_hom]
      erw [← hh]
      simp only [← CategoryTheory.Functor.map_comp_assoc,
        Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
      rfl
  have hnat := compatibleTensorComparison_naturality
    (Etale.derivedTensor A B') (ProEtale.derivedTensor A B') F'
    (ProEtale.comparisonTensorNatIso P.Coefficient B') cd ce
  dsimp only [Functor.whiskeringLeft₂_obj_obj_obj_obj_obj,
    Functor.postcompose₂_obj_obj_obj_obj] at hnat
  have hm₁ := congrArg (fun n ↦ n.app L')
    (ProEtale.comparison_tensor_app P.Coefficient B' K')
  have hm₂ := congrArg (fun n ↦ n.app (G.obj L))
    (ProEtale.comparison_tensor_app P.Coefficient B' (G.obj K))
  dsimp only [K, L, K', L', G, diagonalTwistEtale,
    Etale.ordinaryFinitePullback] at hm₁ hm₂ hnat
  rw [hm₁, hm₂] at hnat
  have hi : m'.symm ≪≫ F'.mapIso
        (compatibleBifunctorIso (Etale.derivedTensor A B') cd ce) =
      compatibleBifunctorIso (ProEtale.derivedTensor A B')
        (F'.mapIso cd) (F'.mapIso ce) ≪≫ m''.symm :=
    compatibleIso_inverse_square m' m''
      (F'.mapIso (compatibleBifunctorIso (Etale.derivedTensor A B') cd ce))
      (compatibleBifunctorIso (ProEtale.derivedTensor A B') (F'.mapIso cd) (F'.mapIso ce))
      (by
        simpa only [compatibleComparisonTensorGeneric, m', m'', K, L, K', L', G,
          diagonalTwistEtale, Etale.ordinaryFinitePullback] using hnat)
  have hc₀ : H.mapIso m.symm ≪≫
        Dnc.pullComparison P b (((Etale.derivedTensor A B).obj K).obj L) ≪≫
        F'.mapIso (Etale.leftDerivedUpperStarTensorIso A b K L) =
      ProEtale.leftDerivedUpperStarTensorIso A b (F.obj K) (F.obj L) ≪≫
        compatibleBifunctorIso (ProEtale.derivedTensor A B')
          (Dnc.pullComparison P b K) (Dnc.pullComparison P b L) ≪≫ m'.symm := by
    simpa only [compatibleBifunctorIso, compatibleComparisonTensorGeneric, m, m',
      Iso.trans_assoc, Functor.comp_obj] using hc
  have ht := compatibleBifunctorIso_trans (ProEtale.derivedTensor A B')
    (Dnc.pullComparison P b K) (F'.mapIso cd) (Dnc.pullComparison P b L) (F'.mapIso ce)
  have hn' := congrArg Iso.hom hn
  have hc' := congrArg Iso.hom hc₀
  have he' := congrArg Iso.hom he
  have hi' := congrArg Iso.hom hi
  have ht' := congrArg Iso.hom ht
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom] at hn' hc' he' hi' ht'
  apply Iso.ext
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    CategoryTheory.Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn']
  rw [← F'.map_comp, he']
  simp only [F'.map_comp]
  rw [reassoc_of% hc', reassoc_of% hi', reassoc_of% ht']

set_option maxHeartbeats 2000000 in
-- The coherence calculation elaborates large tensor and comparison expressions.
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
private theorem tate_square (P : PurityFiniteSetting.{u})
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (j : X' ⟶ X) (v : Y' ⟶ Y) (h : j ≫ f = f' ≫ v)
    (aY : Y ⟶ Spec (.of P.field.k)) (e : ℕ) :
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) j).leftDerivedFunctor.mapIso
        (P.modelOrientationTwistPullback f aY e) ≪≫
      P.modelOrientationTwistPullback j (f ≫ aY) e =
    (ProEtale.leftDerivedUpperStarComp
        (ModuleCat.{u + 1} P.Coefficient) j f).symm.app (P.diagonalTwist Y e) ≪≫
      (ProEtale.leftDerivedUpperStarCongr
        (ModuleCat.{u + 1} P.Coefficient) h).app (P.diagonalTwist Y e) ≪≫
      (ProEtale.leftDerivedUpperStarComp
        (ModuleCat.{u + 1} P.Coefficient) f' v).app (P.diagonalTwist Y e) ≪≫
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f').leftDerivedFunctor.mapIso
        (P.modelOrientationTwistPullback v aY e) ≪≫
      P.modelOrientationTwistPullback f' (v ≫ aY) e := by
  rw [tate_comp]
  have hc := tate_comp P f' v aY (v ≫ aY) e
  have he := tate_congr P h aY e
  apply Iso.ext
  have hch := congrArg Iso.hom hc
  have heh := congrArg Iso.hom he
  simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom] at hch heh ⊢
  rw [hch]
  simp only [Iso.hom_inv_id_app_assoc]
  rw [heh]

set_option maxHeartbeats 2000000 in
-- The coherence calculation elaborates large tensor and comparison expressions.
/-- Pullback of the ordered tensor orientation multiplication along a commuting square.
Source: smooth-purity composition proof, Step 1, model descent Steps 6--9.
(blueprint: lem-pur-model-orientation-mu-pullback).

Proof: The ordinary positive Tate powers are built by adjoining the shifted Tate
line on the right. Induct on the second rank in their concatenation: the zero
case is the unit pullback equation and right unitality of derived pullback; the
successor case is its associativity and naturality. Transport this equation
through the canonical monoidal site comparison. The Tate pullback composition
equation identifies the second factor around the given commuting square.
Naturality of the tensor comparison then composes that factor equation with
the transported concatenation equation. This includes rank zero, and uses no
permutation of the ordered factors. -/
theorem modelOrientationMu_pullback (P : PurityFiniteSetting.{u})
    {X Y X' Y' : Scheme.{u}} (d e : ℕ) (f : X ⟶ Y) (f' : X' ⟶ Y')
    (j : X' ⟶ X) (v : Y' ⟶ Y) (h : j ≫ f = f' ≫ v)
    (aY : Y ⟶ Spec (.of P.field.k)) :
    letI : IsNoetherianRing P.Coefficient := isNoetherian_of_finite _ _
    letI := ProEtale.upperStarPreservesFlat_moduleCat P.Coefficient
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) j).leftDerivedFunctor.mapIso
        (P.modelOrientationMu d e f aY) ≪≫
      P.modelOrientationTwistPullback j (f ≫ aY) (d + e) =
    ProEtale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} P.Coefficient) j
        (P.diagonalTwist X d)
        ((ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.obj
          (P.diagonalTwist Y e)) ≪≫
      P.compatibleTensorIso (P.modelOrientationTwistPullback j (f ≫ aY) d)
        ((ProEtale.leftDerivedUpperStarComp
            (ModuleCat.{u + 1} P.Coefficient) j f).symm.app (P.diagonalTwist Y e) ≪≫
          (ProEtale.leftDerivedUpperStarCongr
            (ModuleCat.{u + 1} P.Coefficient) h).app (P.diagonalTwist Y e) ≪≫
          (ProEtale.leftDerivedUpperStarComp
            (ModuleCat.{u + 1} P.Coefficient) f' v).app (P.diagonalTwist Y e) ≪≫
          (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f').leftDerivedFunctor.mapIso
            (P.modelOrientationTwistPullback v aY e)) ≪≫
      P.modelOrientationMu d e f' (v ≫ aY) := by
  let : IsNoetherianRing P.Coefficient := isNoetherian_of_finite _ _
  let := ProEtale.upperStarPreservesFlat_moduleCat P.Coefficient
  let A := ModuleCat.{u + 1} P.Coefficient
  let H := (ProEtale.upperStar A j).leftDerivedFunctor
  let T := ProEtale.derivedTensor A X'
  have hp := power_mul_pullback P d e j (f ≫ aY)
  have hn := compatibleTensorComparison_naturality
    (P.compatibleTensor X) T H (ProEtale.leftDerivedUpperStarTensorNatIso A j)
    (Iso.refl (P.diagonalTwist X d)) (P.modelOrientationTwistPullback f aY e)
  have ht := tate_square P f f' j v h aY e
  let Q := (ProEtale.leftDerivedUpperStarComp A j f).symm ≪≫
    ProEtale.leftDerivedUpperStarCongr A h ≪≫
      ProEtale.leftDerivedUpperStarComp A f' v
  have hfactor :
      compatibleBifunctorIso T (H.mapIso (Iso.refl (P.diagonalTwist X d)))
          (H.mapIso (P.modelOrientationTwistPullback f aY e)) ≪≫
        compatibleBifunctorIso T (P.modelOrientationTwistPullback j (f ≫ aY) d)
          (P.modelOrientationTwistPullback j (f ≫ aY) e) =
      compatibleBifunctorIso T (P.modelOrientationTwistPullback j (f ≫ aY) d)
          (Q.app (P.diagonalTwist Y e) ≪≫
            (ProEtale.upperStar A f').leftDerivedFunctor.mapIso
              (P.modelOrientationTwistPullback v aY e)) ≪≫
        compatibleBifunctorIso T (Iso.refl (P.diagonalTwist X' d))
          (P.modelOrientationTwistPullback f' (v ≫ aY) e) := by
    rw [Functor.mapIso_refl]
    apply tensor_square_right
    simpa only [Q, NatIso.trans_app, Iso.trans_assoc, H, A] using ht
  let a := P.compatibleTensorIso (Iso.refl (P.diagonalTwist X d))
    (P.modelOrientationTwistPullback f aY e)
  let d₀ := ProEtale.leftDerivedUpperStarTensorIso A j
    (P.diagonalTwist X d) (P.diagonalTwist X e)
  let e₀ := compatibleBifunctorIso T (P.modelOrientationTwistPullback j (f ≫ aY) d)
    (P.modelOrientationTwistPullback j (f ≫ aY) e)
  let f₀ := ProEtale.leftDerivedUpperStarTensorIso A j (P.diagonalTwist X d)
    ((ProEtale.upperStar A f).leftDerivedFunctor.obj (P.diagonalTwist Y e))
  let g₀ := compatibleBifunctorIso T (H.mapIso (Iso.refl (P.diagonalTwist X d)))
    (H.mapIso (P.modelOrientationTwistPullback f aY e))
  let r₀ := compatibleBifunctorIso T (P.modelOrientationTwistPullback j (f ≫ aY) d)
    (Q.app (P.diagonalTwist Y e) ≪≫
      (ProEtale.upperStar A f').leftDerivedFunctor.mapIso
        (P.modelOrientationTwistPullback v aY e))
  let s₀ := P.compatibleTensorIso (Iso.refl (P.diagonalTwist X' d))
    (P.modelOrientationTwistPullback f' (v ≫ aY) e)
  have hn₀ : H.mapIso a ≪≫ d₀ = f₀ ≪≫ g₀ := by
    simpa only [a, d₀, f₀, g₀, compatibleTensorIso, compatibleTensor,
      ProEtale.leftDerivedUpperStarTensorIso, H, T, A,
      diagonalTwist, diagonalTwistEtale] using hn
  have hp₀ : H.mapIso (P.modelOrientationPowerMul X d e) ≪≫
      P.modelOrientationTwistPullback j (f ≫ aY) (d + e) =
      d₀ ≪≫ e₀ ≪≫ P.modelOrientationPowerMul X' d e := by
    simpa only [d₀, e₀, H, A, T, compatibleTensorIso, compatibleTensor] using hp
  have hf₀ : g₀ ≪≫ e₀ = r₀ ≪≫ s₀ := by
    exact hfactor
  have hresult := paste_iso_squares (H.mapIso a)
    (H.mapIso (P.modelOrientationPowerMul X d e))
    (P.modelOrientationTwistPullback j (f ≫ aY) (d + e))
    d₀ e₀ (P.modelOrientationPowerMul X' d e) f₀ g₀ r₀ s₀ hp₀ hn₀ hf₀
  simpa only [modelOrientationMu, a, f₀, r₀, s₀, H, A, T, Q,
    compatibleTensorIso, compatibleTensor, NatIso.trans_app,
    Functor.mapIso_trans, Iso.trans_assoc] using hresult



end WeilConjectures.PurityFiniteSetting
