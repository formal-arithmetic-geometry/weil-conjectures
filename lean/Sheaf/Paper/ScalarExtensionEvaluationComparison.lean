/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P5
-/
module

public import Sheaf.Paper.SemilinearSystemModels
import all Sheaf.Paper.SemilinearDerivedCalculus
import Sheaf.Paper.ScalarExtensionEvaluationPresheaf

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

@[irreducible] private def evaluationExtensionPresheafIso
    (M : Systems.{c, v, max c v r} J B τ) (n : ℕ) :
    SheafOfModules.changeOfRingsPresheaf.{v, c, max c v r}
      (α n) ((evaluation.{c, v, max c v r} J B τ n).obj M) ≅
      (PresheafOfModules.pushforward (F := Prod.sectR n C)
        (eqToHom (evaluation_ring.{c, v, max c v r} J D σ n).symm).hom).obj
          (SheafOfModules.changeOfRingsPresheaf.{v, c, max c v r} φ M) :=
  (scalarExtension_evaluation_presheaf.{c, v, r} J B D τ σ α φ hφ M n).choose

private theorem evaluationExtensionPresheafIso_pure
    (M : Systems.{c, v, max c v r} J B τ) (n : ℕ) (U : Cᵒᵖ)
    (a : (D n).obj.obj U) (x : M.val.obj (op (n, U.unop))) :
    (evaluationExtensionPresheafIso.{c, v, r} J B D τ σ α φ hφ M n).hom.app U
        (a ⊗ₜ[(B n).obj.obj U,((α n).hom.app U).hom] x) =
      (show (systemRing.{c, v, max c v r} J D σ).obj.obj (op (n, U.unop)) from a)
        ⊗ₜ[(B n).obj.obj U,(φ.hom.app (op (n, U.unop))).hom] x := by
  unfold evaluationExtensionPresheafIso
  exact (scalarExtension_evaluation_presheaf.{c, v, r} J B D τ σ α φ hφ M n).choose_spec U a x

private def evaluationExtensionIso
    (S : ScalarData.{c, v, max c v r} φ)
    (M : Systems.{c, v, max c v r} J B τ) (n : ℕ) :
    SheafOfModules.changeOfRings.{v, c, max c v r} (α n) ((evaluation.{c, v, max c v r} J B τ
      n).obj M) ≅
      (evaluation.{c, v, max c v r} J D σ n).obj (S.model.E.obj M) := by
  let ρ := eqToHom (evaluation_ring.{c, v, max c v r} J D σ n).symm
  let P := SheafOfModules.changeOfRingsPresheaf.{v, c, max c v r} φ M
  have : (Prod.sectR n C).IsCocontinuous J (coefficientSequenceTopology J) :=
    ⟨fun hS ↦ hS⟩
  have := restrictionSheafificationMap_isIso ρ P
  exact (PresheafOfModules.sheafification (R := ring.{c, v, max c v r} J (D n)) (𝟙 _)).mapIso
      (evaluationExtensionPresheafIso.{c, v, r} J B D τ σ α φ hφ M n) ≪≫
    asIso (restrictionSheafificationMap ρ P) ≪≫
      (evaluation.{c, v, max c v r} J D σ n).mapIso (eqToIso (S.model.obj_eq M)).symm

private theorem evaluationExtensionIso_unit
    (S : ScalarData.{c, v, max c v r} φ)
    (M : Systems.{c, v, max c v r} J B τ) (n : ℕ) (U : Cᵒᵖ)
    (x : M.val.obj (op (n, U.unop))) :
    (evaluationExtensionIso.{c, v, r} J B D τ σ α φ hφ S M n).hom.val.app U
      (extensionUnit.{c, v, max c v r} (α n) ((evaluation.{c, v, max c v r} J B τ n).obj M) U x) =
    scalarExtensionSection.{c, v, r} φ S M
      (op (n, U.unop)) x := by
  let ρ := eqToHom (evaluation_ring.{c, v, max c v r} J D σ n).symm
  let P := SheafOfModules.changeOfRingsPresheaf.{v, c, max c v r} φ M
  let p := (evaluationExtensionPresheafIso.{c, v, r} J B D τ σ α φ hφ M n).hom
  have hu := congrArg (fun q ↦ q.app U
      ((1 : (D n).obj.obj U) ⊗ₜ[(B n).obj.obj U,((α n).hom.app U).hom] x))
    ((PresheafOfModules.sheafificationAdjunction (R := ring.{c, v, max c v r} J (D n)) (𝟙
      _)).unit.naturality p).symm
  change ((PresheafOfModules.sheafification (R := ring.{c, v, max c v r} J (D n)) (𝟙 _)).map
      p).val.app U
      (extensionUnit.{c, v, max c v r} (α n) ((evaluation.{c, v, max c v r} J B τ n).obj M) U x) =
    ((PresheafOfModules.sheafificationAdjunction (R := ring.{c, v, max c v r} J (D n)) (𝟙
      _)).unit.app
      ((PresheafOfModules.pushforward (F := Prod.sectR n C) ρ.hom).obj P)).app U
        (p.app U ((1 : (D n).obj.obj U) ⊗ₜ[(B n).obj.obj U,((α n).hom.app U).hom] x)) at hu
  change ((eqToHom (S.model.obj_eq M).symm).val.app (op (n, U.unop)))
    ((restrictionSheafificationMap ρ P).val.app U
      (((PresheafOfModules.sheafification (R := ring.{c, v, max c v r} J (D n)) (𝟙 _)).map
      p).val.app U
        (extensionUnit.{c, v, max c v r} (α n) ((evaluation.{c, v, max c v r} J B τ n).obj M) U
      x))) = _
  rw [hu]
  rw [evaluationExtensionPresheafIso_pure.{c, v, r},
    restrictionSheafificationMap_unit_apply]
  rfl

end Construction

attribute [local irreducible] evaluationExtensionIso

/-- Evaluation commutes with ordinary scalar extension, with its section generator fixed.
Source: Stacks Project, Section 03EK and Tag 03CY, restricted to a vertical slice.
(blueprint: lem-sp-scalar-extension-evaluation-comparison).

Proof: the identity on pure tensors identifies the evaluated tensor presheaf with
finite-level scalar extension. The coefficient evaluation maps are identities on
sections and the system morphism has the prescribed components. Naturality follows
from restriction of the two tensor factors. The vertical inclusion is continuous
and cocontinuous, so the existing restriction/sheafification comparison is an
isomorphism. Sheafify the presheaf comparison and transport along S.model.obj_eq.
Naturality of the sheafification unit and the comparison's unit equation give the
displayed value on 1 tensor x. This equation determines the comparison on the locally
generating pure tensors. -/
theorem scalarExtension_evaluation_comparison
    {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
    (J : GrothendieckTopology C)
    (B D : ℕ → Sheaf J CommRingCat.{max c v r})
    (τ : ∀ n, B (n + 1) ⟶ B n) (σ : ∀ n, D (n + 1) ⟶ D n)
    (α : ∀ n, B n ⟶ D n)
    (φ : systemRing.{c, v, max c v r} J B τ ⟶ systemRing.{c, v, max c v r} J D σ)
    (hφ : ∀ (n : ℕ) (U : Cᵒᵖ), φ.hom.app (op (n, U.unop)) = (α n).hom.app U)
    (S : ScalarData.{c, v, max c v r} φ)
    (M : Systems.{c, v, max c v r} J B τ) (n : ℕ) :
    ∃ e : SheafOfModules.changeOfRings.{v, c, max c v r} (α n)
        ((evaluation.{c, v, max c v r} J B τ n).obj M) ≅
          (evaluation.{c, v, max c v r} J D σ n).obj (S.model.E.obj M),
      ∀ (U : Cᵒᵖ) (x : M.val.obj (op (n, U.unop))),
        e.hom.val.app U (extensionUnit.{c, v, max c v r} (α n)
          ((evaluation.{c, v, max c v r} J B τ n).obj M) U x) =
        scalarExtensionSection.{c, v, r}
          φ S M (op (n, U.unop)) x := by
  exact ⟨evaluationExtensionIso.{c, v, r} J B D τ σ α φ hφ S M n,
    evaluationExtensionIso_unit.{c, v, r} J B D τ σ α φ hφ S M n⟩

end WeilConjectures.SemilinearSections

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
