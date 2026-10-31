/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitPullbackData
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorConstraints
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-! # Explicit regular-unit coordinates on the coherent system category

Source: Stacks 07A4 and 0941; the coefficient-unit construction in
`CompletedPullbackTensorUnitFromAssociativity`.
(blueprint: def-pur-completed-unit-tensor-system-data).

The constructions retain the normalized ringed-site unit and its ordinary
pullback multiplication. No isomorphism is chosen from an existence statement
asserting only that the two units are isomorphic.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CompletedUnitPullback

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The closed-system unit in regular single-complex coordinates.
Source: Stacks 07A4, normalized ringed-site tensor unit.
(blueprint: def-pur-completed-unit-tensor-system-data). -/
def tensorSystemUnit (W : Scheme.{u}) :
    (pullbackTensorCalculus l E W).systemClosed.monoidal.tensorUnit ≅
      systemObject l E W := by
  let S := (pullbackTensorCalculus l E W).systemClosed
  let h := ringedDerived_closed_symmetric_monoidal.{u + 1, u, u, u + 2}
    (coefficientSequenceTopology (ProEt.topology W)) (coefficientSequenceCommRingSheaf l E W)
  let S₀ := h.choose
  let h₀ := h.choose_spec.choose_spec.choose_spec.some
  let U := S₀.monoidal.tensorUnit
  let e := (S.adjunction U).leftAdjointUniq (S₀.adjunction U)
  exact (S₀.monoidal.rightUnitor S.monoidal.tensorUnit).symm ≪≫
    (e.app S.monoidal.tensorUnit).symm ≪≫ S.monoidal.leftUnitor U ≪≫ h₀.unitIso

/-- Ordinary pullback multiplication on the actual sequence-ring unit.
Source: Stacks 07A4, pullback of the ring as its rank-one module.
(blueprint: def-pur-completed-unit-tensor-system-data). -/
def tensorSystemRegularPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pullbackTensorSequenceDerived l E f).obj (systemObject l E Y) ≅
      systemObject l E X := by
  let φ := (show ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (coefficientSequenceCommRingSheaf l E Y)) ⟶
      ((pullbackTensorSequenceBase f).sheafPushforwardContinuous RingCat.{u + 1}
        (coefficientSequenceTopology (ProEt.topology Y))
        (coefficientSequenceTopology (ProEt.topology X))).obj
          ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (coefficientSequenceCommRingSheaf l E X)) from
      ⟨Functor.whiskerRight (pullbackTensorSequenceRing l E f).hom
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩)
  letI : (SheafOfModules.pushforward.{u + 1} φ).IsRightAdjoint :=
    pullbackTensorSequenceDirect_rightAdjoint l E f
  letI : (pullbackTensorSequenceBase f).Final := by
    unfold pullbackTensorSequenceBase
    infer_instance
  let j := @asIso _ _ _ _ (SheafOfModules.pullbackObjUnitToUnit φ)
    (SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal
      (F := pullbackTensorSequenceBase f) φ)
  exact ((pullbackTensorSequenceInverse l E f).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor (coefficientSequenceModules l E X) 0).mapIso j

/-- The normalized object comparison, before proving its tensor unitor laws.
Source: Stacks 07A4, coherent coefficient-unit coordinates.
(blueprint: def-pur-completed-unit-tensor-system-data). -/
def tensorSystemPullbackUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pullbackTensorSequenceDerived l E f).obj
        (pullbackTensorCalculus l E Y).systemClosed.monoidal.tensorUnit ≅
      (pullbackTensorCalculus l E X).systemClosed.monoidal.tensorUnit :=
  (pullbackTensorSequenceDerived l E f).mapIso (tensorSystemUnit l E Y) ≪≫
    tensorSystemRegularPullback l E f ≪≫ (tensorSystemUnit l E X).symm

/-- The supplied strict reduction, expressed at the coherent closed-system unit.
Source: Stacks 0941, normalized whole-system comparison.
(blueprint: def-pur-completed-unit-tensor-system-data). -/
def regularTensorSystemComparison (W : Scheme.{u})
    (r : Reduction l E W (calculus l E W)) :
    (pullbackTensorCalculus l E W).reduction.obj
        (integralConstantCoefficientObject l E W) ≅
      (pullbackTensorCalculus l E W).systemClosed.monoidal.tensorUnit :=
  r.comparison ≪≫ (tensorSystemUnit l E W).symm

end WeilConjectures.CompletedUnitPullback
