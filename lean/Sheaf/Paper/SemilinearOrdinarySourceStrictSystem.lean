/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.SemilinearSystemModels
public import Sheaf.CategoryTheory.SystemLevelLeftExtensionBasic

/-! # The prescribed ordinary system as a strict system

Source: Zheng Construction 4.1; Stacks 03D1.
(blueprint: def-coef-ordinary-source-strict-system).

The levels and transitions are literally the existing evaluation and transition operations.
Their strict laws follow from the section formula and the presheaf functor laws.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false
universe c v r
open CategoryTheory Opposite

section
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

namespace WeilConjectures.SemilinearSections.OrdinarySource

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r}) (τ : ∀ n, B (n + 1) ⟶ B n)

-- Keep the section map separate from the coefficient transports during elaboration.
/-- The horizontal map on section carriers, separated from its scalar transports.
Source: Zheng Construction 4.1; the section formula in SemilinearSystemModels.
(blueprint: def-coef-ordinary-source-strict-system). -/
def sourceSection (M : Systems.{c, v, max c v r} J B τ)
    {m n : ℕ} (h : n ≤ m) (U : Cᵒᵖ) :
    M.val.obj (op (m, U.unop)) → M.val.obj (op (n, U.unop)) :=
  fun x ↦ (((transition J B τ h).app M).val.app U) x

private theorem sourceTransition_apply (M : Systems.{c, v, max c v r} J B τ)
    {m n : ℕ} (h : n ≤ m) (U : Cᵒᵖ)
    (x : M.val.obj (op (m, U.unop))) :
    sourceSection.{c, v, r} J B τ M h U x =
      M.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x :=
  congrFun (eq_of_heq ((transition_exists J B τ h).exists.choose_spec M U)) x

attribute [local irreducible] sourceSection

/-- The identity horizontal map acts as the identity on sections.
Source: Zheng Construction 4.1; the section formula in SemilinearSystemModels.
(blueprint: def-coef-ordinary-source-strict-system). -/
theorem sourceStrict_identity (M : Systems.{c, v, max c v r} J B τ)
    (n : ℕ) (U : Cᵒᵖ) (x : M.val.obj (op (n, U.unop))) :
    @Eq (M.val.obj (op (n, U.unop)))
      (sourceSection.{c, v, r} J B τ M (Nat.le_refl n) U x) x := by
  have he : (Prod.mkHom (homOfLE (Nat.le_refl n)) (𝟙 U.unop)).op =
      𝟙 (op (n, U.unop)) := rfl
  have hi : M.val.map (Prod.mkHom (homOfLE (Nat.le_refl n)) (𝟙 U.unop)).op x = x := by
    rw [he, M.val.map_id]
    rfl
  exact (sourceTransition_apply.{c, v, r} J B τ M (Nat.le_refl n) U x).trans hi

/-- Horizontal maps compose as presheaf restrictions.
Source: Zheng Construction 4.1; the section formula in SemilinearSystemModels.
(blueprint: def-coef-ordinary-source-strict-system). -/
theorem sourceStrict_compose (M : Systems.{c, v, max c v r} J B τ)
    {l m n : ℕ} (h : l ≤ m) (k : m ≤ n)
    (U : Cᵒᵖ) (x : M.val.obj (op (n, U.unop))) :
    @Eq (M.val.obj (op (l, U.unop)))
      (sourceSection.{c, v, r} J B τ M (h.trans k) U x)
      (sourceSection.{c, v, r} J B τ M h U
        (sourceSection.{c, v, r} J B τ M k U x)) := by
  have he : (Prod.mkHom (homOfLE (h.trans k)) (𝟙 U.unop)).op =
      (Prod.mkHom (homOfLE k) (𝟙 U.unop)).op ≫
        (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op := by
    apply Quiver.Hom.unop_inj
    apply Prod.hom_ext
    · exact Subsingleton.elim _ _
    · simp
  exact (sourceTransition_apply.{c, v, r} J B τ M (h.trans k) U x).trans
    ((M.val.congr_map_apply he x).trans
      ((M.val.map_comp_apply (Prod.mkHom (homOfLE k) (𝟙 U.unop)).op
        (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x).trans
        ((congrArg (M.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op)
          (sourceTransition_apply.{c, v, r} J B τ M k U x).symm).trans
          (sourceTransition_apply.{c, v, r} J B τ M h U
            (show M.val.obj (op (m, U.unop)) from
              sourceSection.{c, v, r} J B τ M k U x)).symm)))

/-- The strict system with exactly the prescribed evaluations and transitions.
Source: Zheng Construction 4.1; the section formula in SemilinearSystemModels.
(blueprint: def-coef-ordinary-source-strict-system). -/
def sourceStrictObject (M : Systems.{c, v, max c v r} J B τ) :
    SheafOfModules.StrictRingSystem.{c, v, max c v r} (rings J B τ) where
  level n := (evaluation J B τ n).obj M
  transition h := (transition J B τ h).app M
  identity n U x := by
    have he := sourceStrict_identity.{c, v, r} J B τ M n U x
    unfold sourceSection at he
    exact he
  compose h k U x := by
    have he := sourceStrict_compose.{c, v, r} J B τ M h k U x
    unfold sourceSection at he
    exact he

/-- Extraction of strict systems using exactly the prescribed component functors.
Source: Zheng Construction 4.1; the section formula in SemilinearSystemModels.
(blueprint: def-coef-ordinary-source-strict-system). -/
def sourceStrictFunctor : Systems.{c, v, max c v r} J B τ ⥤
    SheafOfModules.StrictRingSystem.{c, v, max c v r} (rings J B τ) where
  obj := sourceStrictObject.{c, v, r} J B τ
  map f :=
    { app := fun n ↦ (evaluation J B τ n).map f
      comm := fun h ↦ (transition J B τ h).naturality f }
  map_id M := by
    apply SheafOfModules.strictRingSystem_hom_ext
    intro n
    exact (evaluation J B τ n).map_id M
  map_comp f g := by
    apply SheafOfModules.strictRingSystem_hom_ext
    intro n
    exact (evaluation J B τ n).map_comp f g

#print axioms sourceStrictFunctor

end WeilConjectures.SemilinearSections.OrdinarySource

end
