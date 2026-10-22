/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S9
-/
module

public import Sheaf.Paper.RationalComparisonStageSystem

/-! # The rational stage system with its original tower maps

Source: blueprint order 1826, conditional construction step 5
(blueprint: lem-sf-rational-comparison-transition-tensor).
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

attribute [local instance] rationalStructures

/-- The transition tensor structure is the literal localization of the integral one.
Source: blueprint order 1826 (blueprint: lem-sf-rational-comparison-transition-tensor). -/
def rationalTransitionCore {E L : Index l Ω} (a : E ≤ L) :
    (rationalTransition A hA a).CoreMonoidal where
  εIso := (ScalarLocalization.localization (Integers l Ω L) (C L)
    (uniformizer l Ω L)).mapIso (A.transitionTensor a).εIso
  μIso X Y := (ScalarLocalization.localization (Integers l Ω L) (C L)
    (uniformizer l Ω L)).mapIso
      ((A.transitionTensor a).μIso X.obj Y.obj)
  μIso_hom_natural_left := by
    intro X Y f Z
    letI := rationalTransition_additive A hA a
    change ScalarLocalization.composition _ _ _ _ _ _
      ((1 : Localization.Away (uniformizer l Ω L)) ⊗ₜ[
          Integers l Ω L] ((A.transitionTensor a).μIso Y.obj Z.obj).hom)
      (ScalarLocalization.tensorMap _ _ _ ((rationalTransition A hA a).map f)
        ((1 : Localization.Away (uniformizer l Ω L)) ⊗ₜ[
          Integers l Ω L] 𝟙 ((A.S.T a).obj Z.obj))) =
      ScalarLocalization.composition _ _ _ _ _ _
        ((rationalTransition A hA a).map (ScalarLocalization.tensorMap _ _ _ f
          (1 ⊗ₜ[Integers l Ω E] 𝟙 Z.obj)))
        ((1 : Localization.Away (uniformizer l Ω L)) ⊗ₜ[
          Integers l Ω L] ((A.transitionTensor a).μIso X.obj Z.obj).hom)
    simp only [rationalTransition_map]
    induction f using TensorProduct.induction_on with
    | zero => simp only [map_zero, ScalarLocalization.tensorMap_zero_left,
        ScalarLocalization.tensorMap_zero_right, LinearMap.zero_apply]
    | add f g hf hg =>
      simp only [map_add, ScalarLocalization.tensorMap_add_left,
        ScalarLocalization.tensorMap_add_right, LinearMap.add_apply, hf, hg]
    | tmul b f =>
      simp only [rationalTransitionHom_tmul, ScalarLocalization.tensorMap_tmul,
        ScalarLocalization.composition_tmul, mul_one, one_mul, tensorHom_id]
      congr 1
      exact (A.transitionTensor a).μIso_hom_natural_left f Z.obj
  μIso_hom_natural_right := by
    intro X Y Z f
    letI := rationalTransition_additive A hA a
    change ScalarLocalization.composition _ _ _ _ _ _
      ((1 : Localization.Away (uniformizer l Ω L)) ⊗ₜ[
          Integers l Ω L] ((A.transitionTensor a).μIso Z.obj Y.obj).hom)
      (ScalarLocalization.tensorMap _ _ _
        ((1 : Localization.Away (uniformizer l Ω L)) ⊗ₜ[
          Integers l Ω L] 𝟙 ((A.S.T a).obj Z.obj))
        ((rationalTransition A hA a).map f)) =
      ScalarLocalization.composition _ _ _ _ _ _
        ((rationalTransition A hA a).map (ScalarLocalization.tensorMap _ _ _
          (1 ⊗ₜ[Integers l Ω E] 𝟙 Z.obj) f))
        ((1 : Localization.Away (uniformizer l Ω L)) ⊗ₜ[
          Integers l Ω L] ((A.transitionTensor a).μIso Z.obj X.obj).hom)
    simp only [rationalTransition_map]
    induction f using TensorProduct.induction_on with
    | zero => simp only [map_zero, ScalarLocalization.tensorMap_zero_left,
        ScalarLocalization.tensorMap_zero_right, LinearMap.zero_apply]
    | add f g hf hg =>
      simp only [map_add, ScalarLocalization.tensorMap_add_left,
        ScalarLocalization.tensorMap_add_right, LinearMap.add_apply, hf, hg]
    | tmul b f =>
      simp only [rationalTransitionHom_tmul, ScalarLocalization.tensorMap_tmul,
        ScalarLocalization.composition_tmul, mul_one, one_mul, id_tensorHom]
      congr 1
      exact (A.transitionTensor a).μIso_hom_natural_right Z.obj f
  associativity X Y Z := by
    change ScalarLocalization.composition _ _ _ _ _ _
      (ScalarLocalization.composition _ _ _ _ _ _
        ((rationalTransition A hA a).map
          (1 ⊗ₜ[Integers l Ω E] (α_ X.obj Y.obj Z.obj).hom))
        (1 ⊗ₜ[Integers l Ω L]
          ((A.transitionTensor a).μIso (X.obj ⊗ Y.obj) Z.obj).hom))
      (ScalarLocalization.tensorMap _ _ _
        (1 ⊗ₜ[Integers l Ω L] ((A.transitionTensor a).μIso X.obj Y.obj).hom)
        (1 ⊗ₜ[Integers l Ω L] 𝟙 ((A.S.T a).obj Z.obj))) =
      ScalarLocalization.composition _ _ _ _ _ _
        (ScalarLocalization.composition _ _ _ _ _ _
          (1 ⊗ₜ[Integers l Ω L]
            ((A.transitionTensor a).μIso X.obj (Y.obj ⊗ Z.obj)).hom)
          (ScalarLocalization.tensorMap _ _ _
            (1 ⊗ₜ[Integers l Ω L] 𝟙 ((A.S.T a).obj X.obj))
            (1 ⊗ₜ[Integers l Ω L] ((A.transitionTensor a).μIso Y.obj Z.obj).hom)))
        (1 ⊗ₜ[Integers l Ω L]
          (α_ ((A.S.T a).obj X.obj) ((A.S.T a).obj Y.obj)
            ((A.S.T a).obj Z.obj)).hom)
    simp only [rationalTransition_map, rationalTransitionHom_tmul, map_one,
      ScalarLocalization.tensorMap_tmul, ScalarLocalization.composition_tmul,
      one_mul, tensorHom_id, id_tensorHom]
    exact congrArg (fun f ↦ (1 : Localization.Away (uniformizer l Ω L)) ⊗ₜ[
      Integers l Ω L] f) ((A.transitionTensor a).associativity X.obj Y.obj Z.obj)
  left_unitality X := by
    change ((1 : Localization.Away (uniformizer l Ω L)) ⊗ₜ[
          Integers l Ω L]
      (λ_ ((A.S.T a).obj X.obj)).hom) =
      ScalarLocalization.composition _ _ _ _ _ _
        (ScalarLocalization.composition _ _ _ _ _ _
          ((rationalTransition A hA a).map
            (1 ⊗ₜ[Integers l Ω E] (λ_ X.obj).hom))
          (1 ⊗ₜ[Integers l Ω L]
            ((A.transitionTensor a).μIso (𝟙_ (C E)) X.obj).hom))
        (ScalarLocalization.tensorMap _ _ _
          (1 ⊗ₜ[Integers l Ω L] (A.transitionTensor a).εIso.hom)
          (1 ⊗ₜ[Integers l Ω L] 𝟙 ((A.S.T a).obj X.obj)))
    simp only [rationalTransition_map, rationalTransitionHom_tmul, map_one,
      ScalarLocalization.tensorMap_tmul, ScalarLocalization.composition_tmul,
      one_mul, tensorHom_id]
    exact congrArg (fun f ↦ (1 : Localization.Away (uniformizer l Ω L)) ⊗ₜ[
      Integers l Ω L] f) ((A.transitionTensor a).left_unitality X.obj)
  right_unitality X := by
    change ((1 : Localization.Away (uniformizer l Ω L)) ⊗ₜ[
          Integers l Ω L]
      (ρ_ ((A.S.T a).obj X.obj)).hom) =
      ScalarLocalization.composition _ _ _ _ _ _
        (ScalarLocalization.composition _ _ _ _ _ _
          ((rationalTransition A hA a).map
            (1 ⊗ₜ[Integers l Ω E] (ρ_ X.obj).hom))
          (1 ⊗ₜ[Integers l Ω L]
            ((A.transitionTensor a).μIso X.obj (𝟙_ (C E))).hom))
        (ScalarLocalization.tensorMap _ _ _
          (1 ⊗ₜ[Integers l Ω L] 𝟙 ((A.S.T a).obj X.obj))
          (1 ⊗ₜ[Integers l Ω L] (A.transitionTensor a).εIso.hom))
    simp only [rationalTransition_map, rationalTransitionHom_tmul, map_one,
      ScalarLocalization.tensorMap_tmul, ScalarLocalization.composition_tmul,
      one_mul, id_tensorHom]
    exact congrArg (fun f ↦ (1 : Localization.Away (uniformizer l Ω L)) ⊗ₜ[
      Integers l Ω L] f) ((A.transitionTensor a).right_unitality X.obj)

end WeilConjectures.TensorComparisonDescent
