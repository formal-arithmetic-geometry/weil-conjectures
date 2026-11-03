/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodReductionRepresentatives.PodReindexingReductionTensorData
public import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingCoherenceData
public import WeilConjectures.SixFunctors.Tensor.TensorReductionStrictComparison
public import WeilConjectures.PoincareDuality.StrictTensorAugmentation.StrictTensorAugmentation

/-! # Extensionality and generator formulas for the strict reduction tensor equation

Source: Stacks 03EK, 03EL, 07A4 and 0941.
(blueprint: lem-pod-reduction-reindex-strict-tensor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PodReductionRepresentatives
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The finite reduction unit inserts the scalar `1`.
Source: Stacks 06YY. -/
theorem finiteAdjunction_unit_apply (W : Scheme.{u}) (n : ℕ)
    (M : integralTowerModules l E W) (U : W.ProEtᵒᵖ) (x : M.val.obj U) :
    ((pullbackTensorFiniteAdjunction l E W n).unit.app M).val.app U x =
      unrestrictedIntegralTensorSection l E W n M U 1 x := by
  have h := (scalarReductionExtension_adjunction l E W n).choose_spec M U x
  exact h.trans rfl

/-- The finite reduction transpose evaluates a map on the unit-inserted section.
Source: Stacks 06YY. -/
theorem finiteAdjunction_homEquiv_apply (W : Scheme.{u}) (n : ℕ)
    (M : integralTowerModules l E W) (N : scalarReductionTarget l E W n)
    (f : (unrestrictedIntegralReductionFunctor l E W n).obj M ⟶ N)
    (U : W.ProEtᵒᵖ) (x : M.val.obj U) :
    (((pullbackTensorFiniteAdjunction l E W n).homEquiv M N f).val.app U) x =
      f.val.app U (unrestrictedIntegralTensorSection l E W n M U 1 x) := by
  rw [Adjunction.homEquiv_unit]
  exact congrArg (f.val.app U) (finiteAdjunction_unit_apply l E W n M U x)


/-- Degreewise, the complex-level reduction evaluation is the termwise one.
Source: Stacks 0941. -/
theorem reductionEvaluationComplex_hom_f (W : Scheme.{u}) (n : ℕ)
    (C : CochainComplex (integralTowerModules l E W) ℤ) (k : ℤ) :
    ((pullbackTensorReductionEvaluationComplex l E W n).hom.app C).f k =
      (pullbackTensorReductionEvaluation l E W n).hom.app (C.X k) := by
  simp [pullbackTensorReductionEvaluationComplex]
  exact Category.comp_id _

/-- Degreewise, the inverse complex-level reduction evaluation is the termwise inverse.
Source: Stacks 0941. -/
theorem reductionEvaluationComplex_inv_f (W : Scheme.{u}) (n : ℕ)
    (C : CochainComplex (integralTowerModules l E W) ℤ) (k : ℤ) :
    ((pullbackTensorReductionEvaluationComplex l E W n).inv.app C).f k =
      (pullbackTensorReductionEvaluation l E W n).inv.app (C.X k) := by
  simp [pullbackTensorReductionEvaluationComplex]
  exact Category.id_comp _

set_option maxHeartbeats 2000000 in
-- Elaborating the sections of the transported reduction maps is expensive.
/-- Maps out of the ordinary reduction of a degree of a total tensor are determined by the
reductions of unit-inserted pure tensors at every level.
Source: Stacks 03EK, 06YY and 0941. -/
theorem reduction_total_hom_ext (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) (k : ℤ)
    {N : coefficientSequenceModules l E W}
    {h₁ h₂ : (pullbackTensorOrdinaryReduction l E W).obj
      (((coefficientTotalTensor.{u, u + 1, u} (ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)).X k) ⟶ N}
    (h : ∀ (n : ℕ) (p q : ℤ) (hpq : p + q = k) (V : W.ProEt)
      (x : (P.X p).val.obj (op V)) (y : (Q.X q).val.obj (op V)),
      h₁.val.app (op (n, V))
        (((pullbackTensorReductionEvaluation l E W n).hom.app _).val.app (op V)
          (unrestrictedIntegralTensorSection l E W n _ (op V) 1
            (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology W)
              (completedIntegralCommRingSheafUnrestricted l E W) P Q p q k hpq (op V) x y))) =
      h₂.val.app (op (n, V))
        (((pullbackTensorReductionEvaluation l E W n).hom.app _).val.app (op V)
          (unrestrictedIntegralTensorSection l E W n _ (op V) 1
            (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology W)
              (completedIntegralCommRingSheafUnrestricted l E W) P Q p q k hpq (op V) x y)))) :
    h₁ = h₂ := by
  have hn (n : ℕ) : (coefficientSequenceEvaluation l E W n).map h₁ =
      (coefficientSequenceEvaluation l E W n).map h₂ := by
    rw [← cancel_epi ((pullbackTensorReductionEvaluation l E W n).hom.app _)]
    apply ((pullbackTensorFiniteAdjunction l E W n).homEquiv _ _).injective
    refine StrictTensorAugmentation.total_hom_ext l E W P Q k
      ((scalarReductionRestriction l E W n).obj ((coefficientSequenceEvaluation l E W n).obj N)) ?_
    intro p q hpq V x y
    have e1 (f : (pullbackTensorOrdinaryReduction l E W).obj
        (((coefficientTotalTensor.{u, u + 1, u} (ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)).X k) ⟶ N)
        (z : ((unrestrictedIntegralReductionFunctor l E W n).obj
          (((coefficientTotalTensor.{u, u + 1, u} (ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)).X k)).val.obj V) :
        (((pullbackTensorReductionEvaluation l E W n).hom.app _ ≫
          (coefficientSequenceEvaluation l E W n).map f).val.app V) z =
        f.val.app (op (n, V.unop))
          (((pullbackTensorReductionEvaluation l E W n).hom.app _).val.app V z) := rfl
    exact (finiteAdjunction_homEquiv_apply l E W n _ _ _ V _).trans ((e1 h₁ _).trans
      ((h n p q hpq V.unop x y).trans ((e1 h₂ _).symm.trans
        (finiteAdjunction_homEquiv_apply l E W n _ _ _ V _).symm)))
  apply SheafOfModules.hom_ext
  ext ⟨n, V⟩ r
  exact congrArg (fun f ↦ f.val.app (op V) r) (hn n)


end WeilConjectures.PodReductionRepresentatives
