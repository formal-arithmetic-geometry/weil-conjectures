/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodCompletedTensorReindex.PodCompletionTensorNormalization
public import WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingReductionTensorSquare
import WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingCoherentTensorRoos
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-! # Descent of the strict tensor limit model

Source: blueprint dual-Tate compatibility, Steps 2 and 4; Stacks 07A4 and 0941.
(blueprint: stage3-pod-reindexing-tensor-limit-model-descent).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] integralCompletedTensor integralCompletedTensorComparison
  podReindexCalculus HasDerivedCategory.standard
  integralOperationsTensorTowerFunctor sfIntegralConstructible

attribute [local irreducible] DerivedCategory instCategoryDerivedCategory podOrdinaryReindex
attribute [local implicit_reducible] integralTowerHasDerivedCategory
  coefficientSequenceHasDerived coefficientFiniteHasDerived
  scalarReductionSourceDerived scalarReductionTargetDerived

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem limitTensorComparison_app
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (A : PodCompletionReindex l E g) (hA : PodCompletionReindex.Laws l E g A)
    (M N : podReindexingDerived l E Y none) :
    let q := podReindexingTensorFrame l E g A hA M N
    HEq (podReindexingLimitTensorComparisonHom l E g A hA M N)
      (q.F.map q.dY.hom ≫ q.δ.app q.U ≫ q.RX.map q.w₁ ≫
        q.RX.map q.w₂ ≫ q.dX.inv) := by
  unfold podReindexingLimitTensorComparisonHom
  rfl

private theorem limitTensorComparison_naturality
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] (A : PodCompletionReindex l E g)
    (hA : PodCompletionReindex.Laws l E g A)
    (M N M' N' : podReindexingDerived l E Y none)
    (f : M ⟶ M') (h : N ⟶ N') :
    (podOrdinaryReindex l E g).map
        ((integralCompletedTensor l E Y).map (Prod.mkHom f h)) ≫
        podReindexingLimitTensorComparisonHom l E g A hA M' N' =
      podReindexingLimitTensorComparisonHom l E g A hA M N ≫
        (integralCompletedTensor l E X).map
          (Prod.mkHom ((podOrdinaryReindex l E g).map f) ((podOrdinaryReindex l E g).map h)) := by
  unfold podReindexingLimitTensorComparisonHom
  dsimp only [podReindexingTensorFrame, Iso.app_hom, Iso.app_inv]
  have hdY := (podReindexingTensorModel l E Y).hom.naturality (Prod.mkHom f h)
  have hdX := (podReindexingTensorModel l E X).inv.naturality
    (Prod.mkHom ((podOrdinaryReindex l E g).map f) ((podOrdinaryReindex l E g).map h))
  have ha := (NatTrans.prod A.reduction.hom A.reduction.hom).naturality (Prod.mkHom f h)
  have hν := (podReindexingSystemTensor l E g).hom.naturality
    (Prod.mkHom ((podReindexCalculus l E Y).reduction.map f)
      ((podReindexCalculus l E Y).reduction.map h))
  have hδ := A.limit.hom.naturality
    ((podReindexCalculus l E Y).systemClosed.tensor.map
      (Prod.mkHom ((podReindexCalculus l E Y).reduction.map f)
        ((podReindexCalculus l E Y).reduction.map h)))
  dsimp only [Functor.comp_map, Functor.prod_map, NatTrans.prod] at hdY hdX ha hν hδ
  rw [← Functor.map_comp_assoc, hdY, Functor.map_comp_assoc]
  rw [reassoc_of% hδ]
  have hνR := congrArg (coefficientSequenceLimit l E X).map hν
  simp only [Functor.map_comp] at hνR
  conv_lhs => rhs; rhs; rw [reassoc_of% hνR]
  have haR := congrArg (fun k ↦ (coefficientSequenceLimit l E X).map
    ((podReindexCalculus l E X).systemClosed.tensor.map k)) ha
  simp only [Functor.map_comp] at haR
  conv_lhs => rhs; rhs; rhs; rw [reassoc_of% haR]
  simp only [Category.assoc]
  conv_lhs => rhs; rhs; rhs; rhs; rw [hdX]

/-- The localization factor with its good-representative endpoints recorded. -/
private def goodReindexFactors
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (A : PodCompletionReindex l E g)
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory) :
    (podOrdinaryReindex l E g).obj (DerivedCategory.Q.obj P.obj) ≅
      DerivedCategory.Q.obj (((podGoodReindex l E g A).obj P).obj) := by
  let : (isoReductionIntegralInverse l E g).Additive :=
    isoSectionwiseModuleInverseImage_additive.{u, u} g (isoReductionCompletedMap l E g).hom
  let : PreservesFiniteLimits (isoReductionIntegralInverse l E g) :=
    isoSectionwiseModuleInverseImage_limits.{u, u} g (isoReductionCompletedMap l E g).hom
  let : PreservesFiniteColimits (isoReductionIntegralInverse l E g) :=
    isoSectionwiseModuleInverseImage_colimits.{u, u} g (isoReductionCompletedMap l E g).hom
  unfold podOrdinaryReindex podGoodReindex
  exact (isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.app P.obj

private theorem frameFinish
    {C D A B : Type*} [Category* C] [Category* D] [Category* A] [Category* B]
    (q : PodTensorAugmentationFrame C D A B) (t : q.F.obj q.CY ⟶ q.CX)
    (h : q.F.map q.dY.hom ≫ q.δ.app q.U ≫ q.RX.map q.w₁ ≫
      q.RX.map q.w₂ ≫ q.dX.inv = t) :
    q.F.map q.dY.hom ≫ q.δ.app q.U ≫ q.RX.map (q.w₁ ≫ q.w₂) = t ≫ q.dX.hom := by
  have he := congrArg (fun f ↦ f ≫ q.dX.hom) h
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Functor.map_comp] using he

/-- Evaluation is equivariant for the contragredient datum under a monoidal
self-equivalence. The inverse datum occurs in the first internal-Hom slot.
The categorical statement applies in particular to the native derived category
of modules over any pulled-back commutative condensed coefficient ring.

Source: latest blueprint prop-pod-dual-tate-data-compatibility, proof Step 2.
Proof: expand the tensor datum and the evaluation-transpose internal-Hom comparison.
Naturality of evaluation moves the datum of B to the output. Dinaturality in A
moves the inverse datum of A to the tensor factor, where it cancels its forward
datum. The defining evaluation equation for the canonical internal-Hom comparison
then gives the tensorator followed by P(evaluation). Cancel the inverse tensorator.
This uses neither dualizability nor boundedness, and also holds for zero objects.
(blueprint: lem-pod-reindexing-contragredient-evaluation). -/
theorem podReindexing_tensor_limit_model_descent
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
    (P : C ⥤ C) [P.Monoidal] [P.IsEquivalence]
    {A B : C} (a : P.obj A ≅ A) (b : P.obj B ≅ B) :
    let c := Functor.Monoidal.ihomObjIso P A B ≪≫
      (MonoidalClosed.internalHom.mapIso a.symm.op).app (P.obj B) ≪≫
      (ihom A).mapIso b
    (Functor.Monoidal.μIso P A ((ihom A).obj B)).inv ≫
      (a.hom ⊗ₘ c.hom) ≫ (ihom.ev A).app B =
        P.map ((ihom.ev A).app B) ≫ b.hom := by
  intro c
  change (Functor.OplaxMonoidal.δ P A ((ihom A).obj B)) ≫
      (a.hom ⊗ₘ ((Functor.LaxMonoidal.ihomComparison P A).natTrans.app B ≫
        (pre a.inv).app (P.obj B) ≫ (ihom A).map b.hom)) ≫
      (ihom.ev A).app B = _
  rw [MonoidalCategory.tensorHom_def a.hom]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [ihom.ev_naturality, id_tensor_pre_app_comp_ev_assoc]
  have hx := MonoidalCategory.whisker_exchange a.inv
    ((Functor.LaxMonoidal.ihomComparison P A).natTrans.app B)
  dsimp only [Functor.comp_obj] at hx
  rw [reassoc_of% hx]
  simp only [← comp_whiskerRight_assoc, a.hom_inv_id, id_whiskerRight, Category.id_comp]
  rw [Functor.LaxMonoidal.ihomComparison_ev_assoc, Functor.Monoidal.δ_μ_assoc]

end WeilConjectures
