/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S9
-/
module

public import Sheaf.Paper.RationalComparisonTransition

/-! # The rational stage system with its original tower maps

Source: blueprint order 1826, conditional construction step 5
(blueprint: lem-sf-rational-comparison-stage-system).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
universe u c h
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct
namespace WeilConjectures.TensorComparisonDescent
attribute [local semireducible] FieldOf integerRing
variable (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω]
variable {l Ω} (C : Index l Ω → Type c) [∀ E, Category.{h} (C E)]
  [∀ E, Preadditive (C E)] [∀ E, Linear (Integers l Ω E) (C E)]
  [∀ E, MonoidalCategory (C E)] [∀ E, SymmetricCategory (C E)]
  [∀ E, MonoidalPreadditive (C E)] [∀ E, MonoidalLinear (Integers l Ω E) (C E)]
variable {C} (A : IntegralData C) (hA : A.Valid)

/-- The integral tower components tensored with one are natural on rational arrows.
Source: blueprint order 1826 (blueprint: lem-sf-rational-comparison-stage-system). -/
def rationalTransitionAssoc {E L M : Index l Ω} (a : E ≤ L) (b : L ≤ M) :
    rationalTransition A hA a ⋙ rationalTransition A hA b ≅
      rationalTransition A hA (a.trans b) :=
  NatIso.ofComponents (fun X ↦
    (ScalarLocalization.localization (Integers l Ω M) (C M) (uniformizer l Ω M)).mapIso
      ((A.S.assoc a b).app X.obj)) (by
    intro X Y f
    letI := rationalTransition_additive A hA a
    letI := rationalTransition_additive A hA b
    letI := rationalTransition_additive A hA (a.trans b)
    change ScalarLocalization.composition (Integers l Ω M) (C M) (uniformizer l Ω M) _ _ _
      (1 ⊗ₜ[Integers l Ω M] (A.S.assoc a b).hom.app Y.obj)
      ((rationalTransition A hA b).map ((rationalTransition A hA a).map f)) =
      ScalarLocalization.composition _ _ _ _ _ _
        ((rationalTransition A hA (a.trans b)).map f)
        (1 ⊗ₜ[Integers l Ω M] (A.S.assoc a b).hom.app X.obj)
    simp only [rationalTransition_map]
    induction f using TensorProduct.induction_on with
    | zero => simp only [Functor.map_zero, map_zero, LinearMap.zero_apply]
    | add f g hf hg => simp only [Functor.map_add, map_add, LinearMap.add_apply, hf, hg]
    | tmul r f =>
      simp only [rationalTransitionHom_tmul, ScalarLocalization.composition_tmul,
        mul_one, one_mul, AlgEquiv.apply_symm_apply]
      have hn := (A.S.assoc a b).hom.naturality f
      dsimp only [Functor.comp_map] at hn
      change _ ⊗ₜ[Integers l Ω M] _ = _ ⊗ₜ[Integers l Ω M] _
      rw [hn]
      rfl)

/-- Rational transitions inherit the complete tower cocycle.
Source: blueprint order 1826 (blueprint: lem-sf-rational-comparison-stage-system). -/
def rationalStageSystem : StageSystem (Rat C) where
  T a := rationalTransition A hA a
  assoc a b := rationalTransitionAssoc A hA a b
  cocycle a b d X := by
    change ScalarLocalization.composition _ _ _ _ _ _
      (1 ⊗ₜ[Integers l Ω _] (A.S.assoc (a.trans b) d).hom.app X.obj)
      ((rationalTransition A hA d).map
        (1 ⊗ₜ[Integers l Ω _] (A.S.assoc a b).hom.app X.obj)) =
      ScalarLocalization.composition _ _ _ _ _ _
        (1 ⊗ₜ[Integers l Ω _] (A.S.assoc a (b.trans d)).hom.app X.obj)
        (1 ⊗ₜ[Integers l Ω _] (A.S.assoc b d).hom.app ((A.S.T a).obj X.obj))
    simp only [rationalTransition_map, rationalTransitionHom_tmul, map_one,
      ScalarLocalization.composition_tmul, one_mul]
    congr 1
    exact A.S.cocycle a b d X.obj

/-- The specified equal-field transition isomorphism is localized component by component.
Source: blueprint order 1826 (blueprint: lem-sf-rational-comparison-stage-system). -/
def rationalTransitionIdentity (E : Index l Ω) :
    rationalTransition A hA (le_refl E) ≅ 𝟭 (Rat C E) :=
  NatIso.ofComponents (fun X ↦
    (ScalarLocalization.localization (Integers l Ω E) (C E) (uniformizer l Ω E)).mapIso
      ((A.identity E).app X.obj)) (by
    intro X Y f
    letI := rationalTransition_additive A hA (le_refl E)
    change ScalarLocalization.composition _ _ _ _ _ _
      (1 ⊗ₜ[Integers l Ω E] (A.identity E).hom.app Y.obj)
      ((rationalTransition A hA (le_refl E)).map f) =
      ScalarLocalization.composition _ _ _ _ _ _ f
        (1 ⊗ₜ[Integers l Ω E] (A.identity E).hom.app X.obj)
    simp only [rationalTransition_map]
    induction f using TensorProduct.induction_on with
    | zero => simp only [Functor.map_zero, map_zero, LinearMap.zero_apply]
    | add f g hf hg => simp only [Functor.map_add, map_add, LinearMap.add_apply, hf, hg]
    | tmul r f =>
      simp only [rationalTransitionHom_tmul, ScalarLocalization.composition_tmul,
        mul_one, one_mul]
      have hn := (A.identity E).hom.naturality f
      dsimp only [Functor.id_map] at hn
      rw [hn]
      change _ ⊗ₜ[Integers l Ω E] _ = r ⊗ₜ[Integers l Ω E] _
      have he : (fieldMap l Ω (le_refl E)).hom (coefficientEquiv l Ω E r) =
          coefficientEquiv l Ω E r := rfl
      rw [he, AlgEquiv.symm_apply_apply])

end WeilConjectures.TensorComparisonDescent
