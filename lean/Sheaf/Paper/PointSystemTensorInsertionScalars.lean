/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module

public import Sheaf.Paper.PointSystemFiniteTensorComparison
import all Sheaf.Paper.PointSystemFiniteTensorComparison
import all Sheaf.Paper.PointSystemEvaluationComparisons
import all Sheaf.Paper.PointRestrictionSystemChainMap

/-! # Scalar actions on tensor insertions

Source: Stacks Tags 03CZ, 03EK and 0941; the tensor-transition step of
`lem-trf-point-system-transport-descent`.
(blueprint: lem-trf-point-system-tensor-insertion-scalars)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
universe t u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.PointSystemTensorTransition
variable (D : FiniteFieldDatum.{t}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (g : Spec (.of D.k) ⟶ Spec (.of D.k)) [IsIso g]

attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  CategoryTheory.sheafCompose coefficientSequenceEvaluation isoSectionwiseModuleInverseImage
  CategoryTheory.Functor.sheafPushforwardContinuous coefficientSequenceCommRingSheaf
  coefficientSequenceCommRingPresheaf coefficientSequenceCommRingSystem

attribute [local irreducible] finiteComparisonMap

private theorem restriction_smul
    {C : Type*} [Category* C] {R : Cᵒᵖ ⥤ RingCat.{v}}
    (M : PresheafOfModules.{v} R) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (a : R.obj X) (x : M.obj X) :
    M.presheaf.map f (a • x) =
      @HSMul.hSMul _ (M.obj Y) (M.obj Y) inferInstance
        (R.map f a) (M.presheaf.map f x) := by
  exact M.map_smul f a x

private theorem pushforward_smul
    {C B : Type*} [Category* C] [Category* B]
    {J : GrothendieckTopology C} {K : GrothendieckTopology B}
    {F : C ⥤ B} [F.IsContinuous J K]
    {R : Sheaf K RingCat.{v}} {S : Sheaf J RingCat.{v}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat J K).obj R)
    (M : SheafOfModules.{v} R)
    (U : Cᵒᵖ) (a : S.obj.obj U) (x : M.val.obj (F.op.obj U)) :
    @HSMul.hSMul _ (((SheafOfModules.pushforward φ).obj M).val.obj U)
        (((SheafOfModules.pushforward φ).obj M).val.obj U) inferInstance a x =
      @HSMul.hSMul _ (M.val.obj (F.op.obj U))
        (M.val.obj (F.op.obj U)) inferInstance (φ.hom.app U a) x := rfl

private theorem pushforward_hom_smul
    {C B : Type*} [Category* C] [Category* B]
    {J : GrothendieckTopology C} {K : GrothendieckTopology B}
    {F : C ⥤ B} [F.IsContinuous J K]
    {R : Sheaf K RingCat.{v}} {S : Sheaf J RingCat.{v}}
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat J K).obj R)
    (M : SheafOfModules.{v} R) {N : SheafOfModules.{v} S}
    (f : (SheafOfModules.pushforward φ).obj M ⟶ N)
    (U : Cᵒᵖ) (a : S.obj.obj U) (x : M.val.obj (F.op.obj U)) :
    f.val.app U
        (@HSMul.hSMul _ (M.val.obj (F.op.obj U))
          (M.val.obj (F.op.obj U)) inferInstance (φ.hom.app U a) x) =
      a • f.val.app U x := by
  exact (f.val.app U).hom.map_smul a x

private theorem evaluation_smul (n : ℕ)
    (M : coefficientSequenceModules l E (Spec (.of D.k)))
    (V : (Spec (.of D.k)).ProEt)
    (a : (integralCoefficientSheaf l E (Spec (.of D.k)) n).obj.obj (op V))
    (x : M.val.obj (op (n, V))) :
    @HSMul.hSMul _
        (((coefficientSequenceEvaluation l E (Spec (.of D.k)) n).obj M).val.obj (op V))
        (((coefficientSequenceEvaluation l E (Spec (.of D.k)) n).obj M).val.obj (op V))
        inferInstance a x =
      @HSMul.hSMul _ (M.val.obj (op (n, V))) (M.val.obj (op (n, V)))
        inferInstance a x := by
  have h := pushforward_smul
    (eqToHom (coefficientSequenceEvaluationRing_eq l E (Spec (.of D.k)) n).symm)
    M (op V) a x
  rw [PointSystemEvaluation.evaluationRing_app D l E n (op V)] at h
  exact h

private theorem insertion_smul (n : ℕ)
    (M : coefficientSequenceModules l E (Spec (.of D.k)))
    (U : (Spec (.of D.k)).ProEt)
    (a : (integralCoefficientSheaf l E (Spec (.of D.k)) n).obj.obj (op U))
    (x : M.val.obj (op (n, (proEtaleIsoPostcompose g).obj U))) :
    insertion D l E g n M U
        (@HSMul.hSMul _ (M.val.obj (op (n, (proEtaleIsoPostcompose g).obj U)))
          (M.val.obj (op (n, (proEtaleIsoPostcompose g).obj U))) inferInstance
          ((inv (inverseImageFiniteCoefficientMap l E g n)).hom.app (op U) a) x) =
      a • insertion D l E g n M U x := by
  have h := pushforward_hom_smul (inv (inverseImageFiniteCoefficientMap l E g n))
    ((coefficientSequenceEvaluation l E (Spec (.of D.k)) n).obj M)
    ((finiteComparisonMap D l E g n).app
      ((coefficientSequenceEvaluation l E (Spec (.of D.k)) n).obj M)) (op U) a x
  have hn (y : ((coefficientSequenceEvaluation l E (Spec (.of D.k)) n).obj M).val.obj
      (op ((proEtaleIsoPostcompose g).obj U))) :
      ((finiteComparisonMap D l E g n).app
        ((coefficientSequenceEvaluation l E (Spec (.of D.k)) n).obj M)).val.app (op U) y =
          insertion D l E g n M U y := by
    dsimp only [insertion]
    exact finiteComparisonMap_normalization D l E g n
      ((coefficientSequenceEvaluation l E (Spec (.of D.k)) n).obj M) U y
  have h' := (hn _).symm.trans (h.trans (congrArg (fun y ↦ a • y) (hn x)))
  rw [evaluation_smul D l E n M ((proEtaleIsoPostcompose g).obj U)] at h'
  exact h'



/-- Scalar multiplication on a tensor insertion uses the inverse coefficient map.
Source: Stacks Tags 03D2 and 03D6; scalar normalization in strict point transport.
(blueprint: lem-trf-point-system-tensor-insertion-scalars).
Proof: the ordinary comparison is linear for the action transported through the
inverse coefficient map. Evaluation uses an equality cast of the coefficient
ring; its recorded component is the identity, so its action is the original
system action. Substitute that identity in linearity and normalize the comparison
on every section. Zero modules and zero scalars are included. -/
theorem tensor_insertion_smul (n : ℕ)
    (M : coefficientSequenceModules l E (Spec (.of D.k)))
    (U : (Spec (.of D.k)).ProEt)
    (a : (integralCoefficientSheaf l E (Spec (.of D.k)) n).obj.obj (op U))
    (x : M.val.obj (op (n, (proEtaleIsoPostcompose g).obj U))) :
    (fun y : M.val.obj (op (n, (proEtaleIsoPostcompose g).obj U)) ↦
      (((integralOperationsLevelPullback.{t, u} l E g n).obj
        ((coefficientSequenceEvaluation l E (Spec (.of D.k)) n).obj M)).val.map
          (proEtaleIsoCommaArrow g U).op)
          (integralOperationsPullbackGenerator l E g n
            ((coefficientSequenceEvaluation l E (Spec (.of D.k)) n).obj M)
            ((proEtaleIsoPostcompose g).obj U) y))
        (@HSMul.hSMul _ (M.val.obj (op (n, (proEtaleIsoPostcompose g).obj U)))
          (M.val.obj (op (n, (proEtaleIsoPostcompose g).obj U))) inferInstance
          ((inv (inverseImageFiniteCoefficientMap l E g n)).hom.app (op U) a) x) =
      a • (fun y : M.val.obj (op (n, (proEtaleIsoPostcompose g).obj U)) ↦
      (((integralOperationsLevelPullback.{t, u} l E g n).obj
        ((coefficientSequenceEvaluation l E (Spec (.of D.k)) n).obj M)).val.map
          (proEtaleIsoCommaArrow g U).op)
          (integralOperationsPullbackGenerator l E g n
            ((coefficientSequenceEvaluation l E (Spec (.of D.k)) n).obj M)
            ((proEtaleIsoPostcompose g).obj U) y)) x := by
  exact insertion_smul D l E g n M U a x

end WeilConjectures.PointSystemTensorTransition
