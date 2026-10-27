/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module

public import Sheaf.Paper.PointRestrictionSystemChainMap
import all Sheaf.Paper.PointSystemFiniteTensorComparison
import all Sheaf.Paper.PointSystemTensorInsertionScalars
import all Sheaf.Paper.PointSystemEvaluationComparisons
import all Sheaf.Paper.PointRestrictionSystemChainMap

/-! # Tensor transitions for strict point systems

Source: Stacks Tags 03CZ, 03EK and 0941; the tensor-transition step of
`lem-trf-point-system-transport-descent`.
(blueprint: lem-trf-point-system-tensor-transition)
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

private abbrev rawLevel (n : ℕ) :=
  pull D l E g ⋙ PointRestrictionSystem.concreteRestriction D l E ⋙
    (evaluation ℕᵒᵖ (scalarReductionSource l E (Spec (.of D.k)))).obj (op n)

private def tensorLevelComparison (n : ℕ) :
    rawLevel D l E g n ≅ tensorLevel D l E g n :=
  Functor.isoWhiskerLeft (pull D l E g)
    (PointSystemEvaluation.levelRestrictionIso D l E n) ≪≫
  (Functor.associator _ _ _).symm ≪≫
  Functor.isoWhiskerRight
    (PointSystemEvaluation.finiteLevelIso D l E g n)
    (scalarReductionRestriction l E (Spec (.of D.k)) n) ≪≫
  Functor.associator _ _ _ ≪≫
  Functor.isoWhiskerLeft (coefficientSequenceEvaluation l E (Spec (.of D.k)) n)
    (Functor.isoWhiskerRight (asIso (finiteComparisonMap D l E g n))
      (scalarReductionRestriction l E (Spec (.of D.k)) n))

private theorem tensorLevelComparison_normalization (n : ℕ)
    (M : coefficientSequenceModules l E (Spec (.of D.k)))
    (U : (Spec (.of D.k)).ProEt)
    (x : M.val.obj (op (n, (proEtaleIsoPostcompose g).obj U))) :
    ((tensorLevelComparison D l E g n).hom.app M).val.app (op U) x =
      insertion D l E g n M U x := by
  change ((finiteComparisonMap D l E g n).app
    ((coefficientSequenceEvaluation l E (Spec (.of D.k)) n).obj M)).val.app (op U) x = _
  dsimp only [insertion]
  exact finiteComparisonMap_normalization D l E g n
    ((coefficientSequenceEvaluation l E (Spec (.of D.k)) n).obj M) U x

attribute [local irreducible] tensorLevelComparison

private def rawTransition (n : ℕ) : rawLevel D l E g (n + 1) ⟶
    rawLevel D l E g n :=
  Functor.whiskerLeft (pull D l E g ⋙ PointRestrictionSystem.concreteRestriction D l E)
    ((evaluation ℕᵒᵖ (scalarReductionSource l E (Spec (.of D.k)))).map
      (homOfLE (Nat.le_succ n)).op)

private def tensorTransitionMap (n : ℕ) :
    tensorLevel D l E g (n + 1) ⟶ tensorLevel D l E g n :=
  (tensorLevelComparison D l E g (n + 1)).inv ≫ rawTransition D l E g n ≫
    (tensorLevelComparison D l E g n).hom

private theorem rawTransition_apply (n : ℕ)
    (M : coefficientSequenceModules l E (Spec (.of D.k)))
    (U : (Spec (.of D.k)).ProEt)
    (x : M.val.obj (op (n + 1, (proEtaleIsoPostcompose g).obj U))) :
    ((rawTransition D l E g n).app M).val.app (op U) x =
      M.val.presheaf.map (Prod.mkHom (homOfLE (Nat.le_succ n))
        (𝟙 ((proEtaleIsoPostcompose g).obj U))).op x := by
  change M.val.presheaf.map (Prod.mkHom (homOfLE (Nat.le_succ n))
    ((proEtaleIsoPostcompose g).map (𝟙 U))).op x = _
  rw [CategoryTheory.Functor.map_id]

private theorem tensorTransitionMap_insertion (n : ℕ)
    (M : coefficientSequenceModules l E (Spec (.of D.k)))
    (U : (Spec (.of D.k)).ProEt)
    (x : M.val.obj (op (n + 1, (proEtaleIsoPostcompose g).obj U))) :
    ((tensorTransitionMap D l E g n).app M).val.app (op U)
        (insertion D l E g (n + 1) M U x) =
      insertion D l E g n M U
        (M.val.presheaf.map (Prod.mkHom (homOfLE (Nat.le_succ n))
          (𝟙 ((proEtaleIsoPostcompose g).obj U))).op x) := by
  have he : (tensorLevelComparison D l E g (n + 1)).hom ≫
      tensorTransitionMap D l E g n =
        rawTransition D l E g n ≫ (tensorLevelComparison D l E g n).hom := by
    dsimp only [tensorTransitionMap]
    simp only [Iso.hom_inv_id_assoc]
  have h := congrArg (fun f ↦ (f.app M).val.app (op U) x) he
  change ((tensorTransitionMap D l E g n).app M).val.app (op U)
      (((tensorLevelComparison D l E g (n + 1)).hom.app M).val.app (op U) x) =
    ((tensorLevelComparison D l E g n).hom.app M).val.app (op U)
      (((rawTransition D l E g n).app M).val.app (op U) x) at h
  simpa only [tensorLevelComparison_normalization, rawTransition_apply] using h


private theorem inverse_coefficient_transition (n : ℕ)
    (U : (Spec (.of D.k)).ProEt)
    (a : (integralCoefficientSheaf l E (Spec (.of D.k)) (n + 1)).obj.obj (op U)) :
    (integralCoefficientSheafTransition l E (Spec (.of D.k)) n).hom.app
        (op ((proEtaleIsoPostcompose g).obj U))
        ((inv (inverseImageFiniteCoefficientMap l E g (n + 1))).hom.app
          (op U) a) =
      (inv (inverseImageFiniteCoefficientMap l E g n)).hom.app
        (op U) ((integralCoefficientSheafTransition l E (Spec (.of D.k)) n).hom.app
          (op U) a) := by
  exact congrArg (fun f ↦ f.hom.app (op U) a)
    (PointRestrictionSystem.inverse_square
      (inverseImageFiniteCoefficientMap l E g (n + 1))
      (inverseImageFiniteCoefficientMap l E g n)
      ((isoSectionwiseInverseImage g RingCat.{max u (t + 1)}).map
        (integralCoefficientSheafTransition l E (Spec (.of D.k)) n))
      (integralCoefficientSheafTransition l E (Spec (.of D.k)) n)
      (PointRestrictionSystem.finite_comparison_naturality D l E g n))

private theorem horizontal_smul (n : ℕ)
    (M : coefficientSequenceModules l E (Spec (.of D.k)))
    (V : (Spec (.of D.k)).ProEt)
    (a : (integralCoefficientSheaf l E (Spec (.of D.k)) (n + 1)).obj.obj (op V))
    (x : M.val.obj (op (n + 1, V))) :
    M.val.presheaf.map (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 V)).op
        (@HSMul.hSMul _ (M.val.obj (op (n + 1, V)))
          (M.val.obj (op (n + 1, V))) inferInstance a x) =
      @HSMul.hSMul _ (M.val.obj (op (n, V)))
          (M.val.obj (op (n, V))) inferInstance
        ((integralCoefficientSheafTransition l E (Spec (.of D.k)) n).hom.app (op V) a)
        (M.val.presheaf.map (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 V)).op x) := by
  have h := restriction_smul M.val
    (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 V)).op a x
  have hc := PointRestrictionSystem.horizontal_map D l E (Nat.le_succ n) (op V)
  have hs : (sequenceRing D l E).obj.map
      (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 V)).op =
      (integralCoefficientSheafTransition l E (Spec (.of D.k)) n).hom.app (op V) := by
    rw [hc]
    simp only [integralCoefficientSheafSystem, Functor.ofOpSequence_map_homOfLE_succ]
  rw [hs] at h
  exact h

private theorem tensorTransitionMap_generators (n : ℕ)
    (M : coefficientSequenceModules l E (Spec (.of D.k)))
    (U : (Spec (.of D.k)).ProEt)
    (a : (integralCoefficientSheaf l E (Spec (.of D.k)) (n + 1)).obj.obj (op U))
    (x : M.val.obj (op (n + 1, (proEtaleIsoPostcompose g).obj U))) :
    ((tensorTransitionMap D l E g n).app M).val.app (op U)
        (@HSMul.hSMul _ (((tensorPull D l E g (n + 1)).obj
            ((coefficientSequenceEvaluation l E (Spec (.of D.k)) (n + 1)).obj M)).val.obj
              (op U))
          (((tensorPull D l E g (n + 1)).obj
            ((coefficientSequenceEvaluation l E (Spec (.of D.k)) (n + 1)).obj M)).val.obj
              (op U)) inferInstance a (insertion D l E g (n + 1) M U x)) =
      @HSMul.hSMul _ (((tensorPull D l E g n).obj
          ((coefficientSequenceEvaluation l E (Spec (.of D.k)) n).obj M)).val.obj (op U))
          (((tensorPull D l E g n).obj
          ((coefficientSequenceEvaluation l E (Spec (.of D.k)) n).obj M)).val.obj (op U))
        inferInstance
        ((integralCoefficientSheafTransition l E (Spec (.of D.k)) n).hom.app (op U) a)
        (insertion D l E g n M U
          (M.val.presheaf.map (Prod.mkHom (homOfLE (Nat.le_succ n))
            (𝟙 ((proEtaleIsoPostcompose g).obj U))).op x)) := by
  rw [← insertion_smul, tensorTransitionMap_insertion, horizontal_smul,
    inverse_coefficient_transition, insertion_smul]


private theorem tensor_transition (n : ℕ) :
    ∃! τ : tensorLevel D l E g (n + 1) ⟶ tensorLevel D l E g n,
      ∀ (M : coefficientSequenceModules l E (Spec (.of D.k)))
        (U : (Spec (.of D.k)).ProEt)
        (a : (integralCoefficientSheaf l E (Spec (.of D.k)) (n + 1)).obj.obj (op U))
        (x : ((coefficientSequenceEvaluation l E (Spec (.of D.k)) (n + 1)).obj M).val.obj
          (op ((proEtaleIsoPostcompose g).obj U))),
        (τ.app M).val.app (op U)
            (@HSMul.hSMul _ (((tensorPull D l E g (n + 1)).obj
                ((coefficientSequenceEvaluation l E (Spec (.of D.k)) (n + 1)).obj M)).val.obj
                  (op U))
          (((tensorPull D l E g (n + 1)).obj
                ((coefficientSequenceEvaluation l E (Spec (.of D.k)) (n + 1)).obj M)).val.obj
                  (op U)) inferInstance a (insertion D l E g (n + 1) M U x)) =
          @HSMul.hSMul _ (((tensorPull D l E g n).obj
              ((coefficientSequenceEvaluation l E (Spec (.of D.k)) n).obj M)).val.obj (op U))
          (((tensorPull D l E g n).obj
              ((coefficientSequenceEvaluation l E (Spec (.of D.k)) n).obj M)).val.obj (op U))
            inferInstance
            ((integralCoefficientSheafTransition l E (Spec (.of D.k)) n).hom.app (op U) a)
            (insertion D l E g n M U
              ((M.val.presheaf.map
                (Prod.mkHom (homOfLE (Nat.le_succ n))
                  (𝟙 ((proEtaleIsoPostcompose g).obj U))).op) x)) := by
  refine ⟨tensorTransitionMap D l E g n, ?_, ?_⟩
  · intro M U a x
    exact tensorTransitionMap_generators D l E g n M U a x
  · intro τ hτ
    apply (Iso.cancel_iso_hom_left (tensorLevelComparison D l E g (n + 1)) _ _).mp
    apply NatTrans.ext
    funext M
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (τ.app M).val.app U
        (((tensorLevelComparison D l E g (n + 1)).hom.app M).val.app U x) = _
    change (τ.app M).val.app U
        (((tensorLevelComparison D l E g (n + 1)).hom.app M).val.app U x) =
      ((tensorTransitionMap D l E g n).app M).val.app U
        (((tensorLevelComparison D l E g (n + 1)).hom.app M).val.app U x)
    rw [tensorLevelComparison_normalization]
    have h := hτ M U.unop 1 x
    have h' := tensorTransitionMap_generators D l E g n M U.unop 1 x
    simpa only [one_smul, map_one] using h.trans h'.symm


/-- The original quotient transition transported to the finite tensor-pullback model.
Source: Stacks Tags 03CZ, 03EK and 0941, and step 3 of
`lem-trf-point-system-transport-descent`.
(blueprint: lem-trf-point-system-tensor-transition).
Proof: identify the reindexed system evaluated at n with finite inverse image,
using the identity comparison on all section carriers. The tensor-unit comparison
is a natural isomorphism. Restrict its scalars through the completed projection and
conjugate the original horizontal transition by these isomorphisms. The inverted
coefficient reduction square and quotient-linearity give the displayed formula on
a times an insertion. Taking a=1 specifies the morphism on every section, since
the tensor-unit comparison is an isomorphism; this proves uniqueness. The argument
allows the identity automorphism, zero modules, and zero or arbitrary transitions. -/
theorem tensor_transition_existsUnique (n : ℕ) :
    ∃! τ :
      (coefficientSequenceEvaluation l E (Spec (.of D.k)) (n + 1) ⋙
        integralOperationsLevelPullback.{t, u} l E g (n + 1) ⋙
          scalarReductionRestriction l E (Spec (.of D.k)) (n + 1)) ⟶
      (coefficientSequenceEvaluation l E (Spec (.of D.k)) n ⋙
        integralOperationsLevelPullback.{t, u} l E g n ⋙
          scalarReductionRestriction l E (Spec (.of D.k)) n),
      ∀ (M : coefficientSequenceModules l E (Spec (.of D.k)))
        (U : (Spec (.of D.k)).ProEt)
        (a : (integralCoefficientSheaf l E (Spec (.of D.k)) (n + 1)).obj.obj (op U))
        (x : ((coefficientSequenceEvaluation l E (Spec (.of D.k)) (n + 1)).obj M).val.obj
          (op ((proEtaleIsoPostcompose g).obj U))),
        (τ.app M).val.app (op U)
          (a • (((integralOperationsLevelPullback.{t, u} l E g (n + 1)).obj
            ((coefficientSequenceEvaluation l E (Spec (.of D.k)) (n + 1)).obj M)).val.map
              (proEtaleIsoCommaArrow g U).op
                (integralOperationsPullbackGenerator l E g (n + 1)
                  ((coefficientSequenceEvaluation l E (Spec (.of D.k)) (n + 1)).obj M)
                  ((proEtaleIsoPostcompose g).obj U) x))) =
          (integralCoefficientSheafTransition l E (Spec (.of D.k)) n).hom.app (op U) a •
            (((integralOperationsLevelPullback.{t, u} l E g n).obj
              ((coefficientSequenceEvaluation l E (Spec (.of D.k)) n).obj M)).val.map
                (proEtaleIsoCommaArrow g U).op
                  (integralOperationsPullbackGenerator l E g n
                    ((coefficientSequenceEvaluation l E (Spec (.of D.k)) n).obj M)
                    ((proEtaleIsoPostcompose g).obj U)
                    (M.val.presheaf.map
                      (Prod.mkHom (homOfLE (Nat.le_succ n))
                        (𝟙 ((proEtaleIsoPostcompose g).obj U))).op x))) := by
  exact tensor_transition D l E g n

end WeilConjectures.PointSystemTensorTransition
