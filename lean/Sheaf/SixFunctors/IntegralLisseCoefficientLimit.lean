/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.SixFunctors.IntegralLisseReductionData
import Sheaf.NumberTheory.Padics.IntegersProfiniteTower
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# The coefficient reduction cone is limiting

Source: Bhatt--Scholze, Lemma 6.8.2(1), pp. 58--59.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

/-- The canonical compatible coefficient reductions. -/
def integralLisseCoefficientCone :
    (Functor.const ℕᵒᵖ).obj (lisseIntegerSheafSized l E X) ⟶
      integralLisseFiniteDiagram l E X :=
  NatTrans.ofOpSequence (integralLisseReduction l E X) (fun n ↦ by
    simp only [Functor.const_obj_map, integralLisseFiniteDiagram,
      Functor.ofOpSequence_map_homOfLE_succ]
    ext U f
    rfl)

/-- The coefficient reduction cone is limiting.

Source: Bhatt--Scholze, Lemma 6.8.2(1), pp. 58--59.
(blueprint: lem-sfb-integral-lisse-coefficient-limit)

Proof: identify the integer coefficient ring with its compatible finite quotient
sequences by the profinite tower theorem and verify the universal property pointwise. -/
theorem integralLisseCoefficient_isLimit :
    Nonempty (IsLimit (Cone.mk _ (integralLisseCoefficientCone l E X))) := by
  classical
  let := spectralNorm.normedField ℚ_[l] E
  obtain ⟨e, he, heHome⟩ :=
    (Padic.coefficientExtension_integers_profinite_tower.{u + 1, u + 1} l E).1
  let t := Padic.coefficientExtensionPositiveLimitTopology l E
  have hq (n : ℕ) : @Continuous _ _
      (inferInstance : TopologicalSpace (Padic.coefficientExtensionIntegers l E)) ⊥
      (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))) := by
    let : ∀ n : ℕ, TopologicalSpace (Padic.coefficientExtensionRing l E (n + 1)) :=
      fun _ ↦ ⊥
    have hc := (continuous_apply n).comp (continuous_subtype_val.comp heHome.continuous)
    exact hc.congr (fun x ↦ he x n)
  have hd (n : ℕ) : @Continuous _ _
      (inferInstance : TopologicalSpace (Padic.coefficientExtensionRing l E (n + 1))) ⊥
      id := by
    exact (@Topology.IsQuotientMap.continuous_iff
      (Padic.coefficientExtensionIntegers l E)
      (Padic.coefficientExtensionRing l E (n + 1))
      (Padic.coefficientExtensionRing l E (n + 1))
      (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))) id _ _ ⊥
      (QuotientRing.isOpenQuotientMap_mk
        (Padic.coefficientExtensionIdeal l E (n + 1))).isQuotientMap).mpr (hq n)
  let : ReflectsLimitsOfShape ℕᵒᵖ (forget CommRingCat.{u + 1}) :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  refine ⟨isLimitOfReflects (sheafToPresheaf (Scheme.ProEt.topology X) CommRingCat)
    (evaluationJointlyReflectsLimits _ fun U ↦ ?_)⟩
  apply isLimitOfReflects (forget CommRingCat)
  apply Classical.choice
  apply (Types.isLimit_iff _).mpr
  intro f hf
  let b : U.unop.left → Padic.coefficientExtensionPositiveLimit l E := fun x ↦
    ⟨fun n ↦ (f (op n)).down x, by
      simp only [Padic.coefficientExtensionPositiveLimit, Subring.mem_iInf,
        RingHom.mem_eqLocus, RingHom.comp_apply, Pi.evalRingHom_apply]
      intro n
      have h := congrArg (fun z ↦ z.down x) (hf (homOfLE (Nat.le_succ n)).op)
      simp only [Functor.comp_map, integralLisseFiniteDiagram,
        Functor.ofOpSequence_map_homOfLE_succ] at h
      change (Padic.coefficientExtensionTransition l E (n + 1))
        ((f (op (n + 1))).down x) = (f (op n)).down x at h
      exact h⟩
  have hc (n : ℕ) : @Continuous _ _ _ ⊥ (fun x ↦ (f (op n)).down x) := by
    apply continuous_def.mpr
    intro V hV
    exact (f (op n)).down.continuous.isOpen_preimage _
      (continuous_def.mp (hd n) V hV)
  have hb : @Continuous _ _ _ t b := by
    let : ∀ n : ℕ, TopologicalSpace (Padic.coefficientExtensionRing l E (n + 1)) :=
      fun _ ↦ ⊥
    exact (continuous_pi hc).subtype_mk _
  have hs : @Continuous _ _ t _ e.symm := by
    let : TopologicalSpace (Padic.coefficientExtensionPositiveLimit l E) := t
    exact e.toEquiv.continuous_symm_iff.mpr heHome.isOpenMap
  let a : (lisseIntegerSheafSized l E X).obj.obj U :=
    ULift.up ⟨fun x ↦ e.symm (b x), hs.comp hb⟩
  refine ⟨a, ?_, ?_⟩
  · intro n
    apply ULift.ext
    apply ContinuousMap.ext
    intro x
    change Ideal.Quotient.mk _ (e.symm (b x)) = (f n).down x
    rw [← he, e.apply_symm_apply]
  · intro a' ha'
    apply ULift.ext
    apply ContinuousMap.ext
    intro x
    apply e.injective
    apply Subtype.ext
    funext n
    rw [he, he]
    have h := congrArg (fun z ↦ z.down x) (ha' (op n))
    change Ideal.Quotient.mk _ (a'.down x) = _ at h
    change Ideal.Quotient.mk _ (a'.down x) =
      Ideal.Quotient.mk _ (e.symm (b x))
    rw [h, ← he, e.apply_symm_apply]

end AlgebraicGeometry.ProEtale
