/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P5
-/
module

public import Sheaf.Paper.SemilinearSystemModels
import Sheaf.Paper.ScalarExtensionEvaluationObjects
import Sheaf.Paper.ScalarExtensionEvaluationNaturality

/-! # Tensor comparison for evaluated scalar extension

Source: Stacks Project, Modules on Sites, Section 03EK and Tag 03CY,
applied to the vertical sequence topology.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe c v r
open CategoryTheory Opposite
namespace WeilConjectures.SemilinearSections

open scoped ChangeOfRings

section Construction
variable {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
  (J : GrothendieckTopology C)
  (B D : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n, B (n + 1) ⟶ B n) (σ : ∀ n, D (n + 1) ⟶ D n)
  (α : ∀ n, B n ⟶ D n)
  (φ : systemRing.{c, v, max c v r} J B τ ⟶ systemRing.{c, v, max c v r} J D σ)
  (hφ : ∀ (n : ℕ) (U : Cᵒᵖ), φ.hom.app (op (n, U.unop)) = (α n).hom.app U)

include hφ

@[irreducible] private def evaluationExtensionPresheafObjIso
    (M : Systems.{c, v, max c v r} J B τ) (n : ℕ) (U : Cᵒᵖ) :
    (SheafOfModules.changeOfRingsPresheaf.{v, c, max c v r}
      (α n) ((evaluation.{c, v, max c v r} J B τ n).obj M)).obj U ≅
      ((PresheafOfModules.pushforward (F := Prod.sectR n C)
        (eqToHom (evaluation_ring.{c, v, max c v r} J D σ n).symm).hom).obj
          (SheafOfModules.changeOfRingsPresheaf.{v, c, max c v r}
            φ M)).obj U :=
  (scalarExtension_evaluation_objects.{c, v, r} J B D τ σ α φ hφ M n).choose U

private theorem evaluationExtensionPresheafObjIso_pure
    (M : Systems.{c, v, max c v r} J B τ) (n : ℕ) (U : Cᵒᵖ)
    (a : (D n).obj.obj U) (x : M.val.obj (op (n, U.unop))) :
    (evaluationExtensionPresheafObjIso.{c, v, r} J B D τ σ α φ hφ M n U).hom
        (a ⊗ₜ[(B n).obj.obj U,((α n).hom.app U).hom] x) =
      (show (systemRing.{c, v, max c v r} J D σ).obj.obj (op (n, U.unop)) from a)
        ⊗ₜ[(B n).obj.obj U,(φ.hom.app (op (n, U.unop))).hom] x := by
  unfold evaluationExtensionPresheafObjIso
  exact (scalarExtension_evaluation_objects.{c, v, r} J B D τ σ α φ hφ M n).choose_spec U a x

@[irreducible] private def evaluationExtensionPresheafIso
    (M : Systems.{c, v, max c v r} J B τ) (n : ℕ) :
    SheafOfModules.changeOfRingsPresheaf.{v, c, max c v r}
      (α n) ((evaluation.{c, v, max c v r} J B τ n).obj M) ≅
      (PresheafOfModules.pushforward (F := Prod.sectR n C)
        (eqToHom (evaluation_ring.{c, v, max c v r} J D σ n).symm).hom).obj
          (SheafOfModules.changeOfRingsPresheaf.{v, c, max c v r}
            φ M) := by
  refine PresheafOfModules.isoMk
    (evaluationExtensionPresheafObjIso.{c, v, r} J B D τ σ α φ hφ M n) ?_
  intro U V f
  exact scalarExtension_evaluation_naturality.{c, v, r} J B D τ σ α φ M n
    (evaluationExtensionPresheafObjIso.{c, v, r} J B D τ σ α φ hφ M n)
    (evaluationExtensionPresheafObjIso_pure.{c, v, r} J B D τ σ α φ hφ M n) f

/-- The evaluated tensor-presheaf comparison sends pure tensors to themselves.
Source: Stacks Project, Section 03EK, naturality of the tensor presheaf.

Proof: use the sectionwise tensor comparisons. Restriction sends a pure tensor to
the tensor of the restrictions of its two factors, so these comparisons are natural.
Their generator formula is the sectionwise comparison's pure-tensor equation. -/
private theorem evaluationExtensionPresheafIso_pure
    (M : Systems.{c, v, max c v r} J B τ) (n : ℕ) (U : Cᵒᵖ)
    (a : (D n).obj.obj U) (x : M.val.obj (op (n, U.unop))) :
    (evaluationExtensionPresheafIso.{c, v, r} J B D τ σ α φ hφ M n).hom.app U
        (a ⊗ₜ[(B n).obj.obj U,((α n).hom.app U).hom] x) =
      (show (systemRing.{c, v, max c v r} J D σ).obj.obj (op (n, U.unop)) from a)
        ⊗ₜ[(B n).obj.obj U,(φ.hom.app (op (n, U.unop))).hom] x := by
  unfold evaluationExtensionPresheafIso
  exact evaluationExtensionPresheafObjIso_pure.{c, v, r} J B D τ σ α φ hφ M n U a x

/-- Evaluation commutes with the tensor presheaf, preserving its generators.
Source: Stacks Project, Section 03EK, restriction in the tensor presheaf.
(blueprint: lem-sp-scalar-extension-evaluation-presheaf).

Proof: take the sectionwise tensor isomorphisms. Both restriction operations
send a pure tensor to the tensor of its restricted factors. Testing on the
generators 1 tensor x proves naturality. The pure-tensor formula is unchanged. -/
theorem scalarExtension_evaluation_presheaf
    (M : Systems.{c, v, max c v r} J B τ) (n : ℕ) :
    ∃ e :
    SheafOfModules.changeOfRingsPresheaf.{v, c, max c v r}
      (α n) ((evaluation.{c, v, max c v r} J B τ n).obj M) ≅
      (PresheafOfModules.pushforward (F := Prod.sectR n C)
        (eqToHom (evaluation_ring.{c, v, max c v r} J D σ n).symm).hom).obj
          (SheafOfModules.changeOfRingsPresheaf.{v, c, max c v r} φ M),
      ∀ (U : Cᵒᵖ) (a : (D n).obj.obj U) (x : M.val.obj (op (n, U.unop))),
        e.hom.app U (a ⊗ₜ[(B n).obj.obj U,((α n).hom.app U).hom] x) =
          (show (systemRing.{c, v, max c v r} J D σ).obj.obj (op (n, U.unop)) from a)
            ⊗ₜ[(B n).obj.obj U,(φ.hom.app (op (n, U.unop))).hom] x := by
  exact ⟨evaluationExtensionPresheafIso.{c, v, r} J B D τ σ α φ hφ M n,
    evaluationExtensionPresheafIso_pure.{c, v, r} J B D τ σ α φ hφ M n⟩

end Construction

end WeilConjectures.SemilinearSections

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
