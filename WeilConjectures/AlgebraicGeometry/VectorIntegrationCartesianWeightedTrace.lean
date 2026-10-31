/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorIntegrationCartesianTensorDescent
public import WeilConjectures.AlgebraicGeometry.ShriekTensorCompositionSupplement

import WeilConjectures.AlgebraicGeometry.VectorIntegrationCartesianProjectionCounit
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
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comp

import all Mathlib.CategoryTheory.Limits.HasLimits

/-! # Weighted trace on a Cartesian affine chart

Source: blueprint sec-smooth-purity/sk-prop-an/cor-pur-vector-bundle-purity.proof.md,
paragraph 2, simultaneous trivializations and ordered affine counits.
(blueprint: lem-pur-vector-integration-cartesian-weighted-trace).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local irreducible] rightDerivedLowerShriek upperStar
  VectorBundleZeroSection.π VectorBundleZeroSection.scheme leftDerivedUpperStarComp
  leftDerivedUpperStarIsoMapDerivedCategory
attribute [local implicit_reducible] Scheme.Modules
  ordinaryFiniteDegreeZero ordinaryFiniteSingleFunctor derivedTensorRight

open MonoidalCategory
attribute [local instance] Sheaf.monoidalCategory
attribute [local irreducible] _root_.DerivedCategory.singleFunctors
  Functor.leftDerivedFunctor

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

set_option maxRecDepth 4096 in
private theorem pullback_right_unitor
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (K : DerivedCategoryModule A Y) :
    (ordinaryFinitePullback A f).map (derivedTensorSingleUnitIso K).hom =
      (ordinaryFiniteTensorPullback A f K (ordinaryFiniteUnit A Y)).hom ≫
      ((ordinaryFiniteTensor A X).obj ((ordinaryFinitePullback A f).obj K)).map
        (ordinaryFiniteUnitPullback A f).hom ≫
      (derivedTensorSingleUnitIso ((ordinaryFinitePullback A f).obj K)).hom := by
  let F := ordinaryFinitePullback A f
  let : F.OplaxMonoidal := leftDerivedUpperStarOplaxMonoidal (ModuleCat.{u + 1} A) f
  have hunit : (ordinaryFiniteUnitPullback A f).hom ≫
      (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) X).hom =
    F.map (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) Y).hom ≫
      Functor.OplaxMonoidal.η F := by
    dsimp only [F, ordinaryFinitePullback]
    rw [leftDerivedUpperStarOplaxMonoidal_η]
    exact ordinaryFiniteUnitPullback_hom_unit A f
  have hz := tensor_zero F
    (show ordinaryFiniteUnit A Y ≅ 𝟙_ (DerivedCategoryModule A Y) from
      singleFunctorObjUnitIso (ModuleCat.{u + 1} A) Y)
    (show ordinaryFiniteUnit A X ≅ 𝟙_ (DerivedCategoryModule A X) from
      singleFunctorObjUnitIso (ModuleCat.{u + 1} A) X)
    (𝟙 (F.obj K)) (ordinaryFiniteUnitPullback A f).hom hunit
  have htensor : (ordinaryFiniteTensorPullback A f K (ordinaryFiniteUnit A Y)).hom =
      Functor.OplaxMonoidal.δ F K (ordinaryFiniteUnit A Y) := by rfl
  have hi : F.map (derivedTensorSingleUnitIso K).inv ≫
      (ordinaryFiniteTensorPullback A f K (ordinaryFiniteUnit A Y)).hom ≫
      ((ordinaryFiniteTensor A X).obj (F.obj K)).map
        (ordinaryFiniteUnitPullback A f).hom =
      (derivedTensorSingleUnitIso (F.obj K)).inv := by
    rw [htensor]
    change F.map ((ρ_ K).inv ≫
        K ◁ (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) Y).inv) ≫
        Functor.OplaxMonoidal.δ F K (ordinaryFiniteUnit A Y) ≫
        F.obj K ◁ (ordinaryFiniteUnitPullback A f).hom =
      (ρ_ (F.obj K)).inv ≫
        F.obj K ◁ (singleFunctorObjUnitIso (ModuleCat.{u + 1} A) X).inv
    dsimp only [ordinaryFiniteUnit, ordinaryFiniteDegreeZero, ordinaryFiniteConstant] at hz ⊢
    simp only [id_tensorHom, Category.id_comp] at hz
    convert hz using 1
    rfl
  apply (cancel_epi (F.map (derivedTensorSingleUnitIso K).inv)).mp
  rw [← F.map_comp, Iso.inv_hom_id, F.map_id]
  simpa only [Category.assoc, Iso.inv_hom_id] using
    (congrArg (fun z => z ≫ (derivedTensorSingleUnitIso (F.obj K)).hom) hi).symm

/-- Weighted trace on a Cartesian affine chart.
Source: blueprint vector-bundle purity proof, paragraph 2.
(blueprint: lem-pur-vector-integration-cartesian-weighted-trace).

Proof: Cancel the pulled-back forward projection. The canonical projection/counit identity
vectorIntegrationCartesianProjectionCounit gives the forward composite, with no arbitrary trace
or inverse projection. Naturality of tensor pullback moves the given map k through its tensor
comparison. Compatibility of pullback with the right unitor follows from oplax unitality and
ordinaryFiniteUnitPullback_hom_unit. The normalization hk identifies the remaining unit trace.
Cancel the projection using its specified inverse. This also covers rank zero, the empty base
and the zero coefficient ring.
-/
theorem vectorIntegrationCartesianWeightedTrace
    (N : ℕ) (hN : 0 < N) (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    {X S T : Scheme.{u}} [IsNoetherian T]
    (p : X ⟶ S) [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p]
    [HasCompactification p] (f : T ⟶ S) (hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ)
    (q : affineTraceTower T d ⟶ X)
    (sq : IsPullback q (affineTraceProjection T d) p f)
    (L K : DerivedCategoryModule A S) (K' : DerivedCategoryModule A T)
    (cK : (ordinaryFinitePullback A f).obj K ≅ K')
    (b : (ordinaryFinitePullback A f).obj L ≅ affineLinearBaseCoefficient A N hA T d)
    (k : (rightDerivedLowerShriek (ModuleCat.{u + 1} A) p).obj
      ((ordinaryFinitePullback A p).obj L) ⟶ ordinaryFiniteUnit A S)
    (hk : (ordinaryFinitePullback A f).map k ≫ (ordinaryFiniteUnitPullback A f).hom =
      vectorIntegrationCartesianPrefix N hN A hA t p f hT d q sq L b ≫
        affineTraceCounit A N hA t D T hT d)
    [hP : IsIso (compactSupportProjectionMap A p ((ordinaryFinitePullback A p).obj L) K)] :
    (ordinaryFinitePullback A f).map
      (@inv _ _ _ _ (compactSupportProjectionMap A p
          ((ordinaryFinitePullback A p).obj L) K) hP ≫
        ((ordinaryFiniteTensor A S).obj K).map k ≫ (derivedTensorSingleUnitIso K).hom) ≫ cK.hom =
    (rightDerivedLowerShriekBaseChangeMap A sq).app _ ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection T d)).map
        (vectorIntegrationCartesianTensorDescent A N hA t p f hT d q sq L K K' cK b).inv ≫
      (affineTraceUnboundedCompactComparison A T d).inv.app _ ≫
      (affineTraceAdjunction A N hA t D T hT d).counit.app
        K' := by
  let F := ordinaryFinitePullback A f
  have hδ' : F.map (((ordinaryFiniteTensor A S).obj K).map k) ≫
      (ordinaryFiniteTensorPullback A f K (ordinaryFiniteUnit A S)).hom =
    (ordinaryFiniteTensorPullback A f K
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) p).obj
        ((ordinaryFinitePullback A p).obj L))).hom ≫
      ((ordinaryFiniteTensor A T).obj (F.obj K)).map (F.map k) := by
    exact leftDerivedUpperStarTensorIso_hom_naturality_right
      f K k
  apply (cancel_epi (F.map
    (compactSupportProjectionMap A p ((ordinaryFinitePullback A p).obj L) K))).mp
  dsimp only [F] at hδ' ⊢
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, IsIso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
  calc
    _ = (ordinaryFiniteTensorPullback A f K
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) p).obj
          ((ordinaryFinitePullback A p).obj L))).hom ≫
        ((ordinaryFiniteTensor A T).obj ((ordinaryFinitePullback A f).obj K)).map
          (vectorIntegrationCartesianPrefix N hN A hA t p f hT d q sq L b ≫
            affineTraceCounit A N hA t D T hT d) ≫
        (derivedTensorSingleUnitIso ((ordinaryFinitePullback A f).obj K)).hom ≫ cK.hom := by
      rw [pullback_right_unitor]
      simp only [Category.assoc]
      rw [reassoc_of% hδ', ← Functor.map_comp_assoc, hk]
    _ = _ := (vectorIntegrationCartesianProjectionCounit
      N hN A hA t D p f hT d q sq L K K' cK b).symm

end AlgebraicGeometry.Etale
