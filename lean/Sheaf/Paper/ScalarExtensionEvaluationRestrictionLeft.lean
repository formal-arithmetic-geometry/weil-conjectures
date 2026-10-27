/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P5
-/
module

public import Sheaf.Paper.SemilinearSystemModels
import all Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction

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
  (M : Systems.{c, v, max c v r} J B τ) (n : ℕ)
  (e : ∀ U : Cᵒᵖ,
    (SheafOfModules.changeOfRingsPresheaf.{v, c, max c v r}
      (α n) ((evaluation.{c, v, max c v r} J B τ n).obj M)).obj U ≅
      ((PresheafOfModules.pushforward (F := Prod.sectR n C)
        (eqToHom (evaluation_ring.{c, v, max c v r} J D σ n).symm).hom).obj
          (SheafOfModules.changeOfRingsPresheaf.{v, c, max c v r} φ M)).obj U)
  (he : ∀ (U : Cᵒᵖ) (a : (D n).obj.obj U) (x : M.val.obj (op (n, U.unop))),
    (e U).hom (a ⊗ₜ[(B n).obj.obj U,((α n).hom.app U).hom] x) =
      (show (systemRing.{c, v, max c v r} J D σ).obj.obj (op (n, U.unop)) from a)
        ⊗ₜ[(B n).obj.obj U,(φ.hom.app (op (n, U.unop))).hom] x)

include he

set_option maxHeartbeats 800000 in
-- The two identity coefficient transports require substantial kernel normalization.
private theorem evaluatedTensorRestriction_left
    {U V : Cᵒᵖ} (f : U ⟶ V)
    (x : ((evaluation.{c, v, max c v r} J B τ n).obj M).val.obj U) :
    (e V).hom
      ((SheafOfModules.changeOfRingsPresheaf.{v, c, max c v r} (α n)
        ((evaluation.{c, v, max c v r} J B τ n).obj M)).map f
          ((1 : (D n).obj.obj U) ⊗ₜ[(B n).obj.obj U,((α n).hom.app U).hom] x)) =
    (1 : (systemRing.{c, v, max c v r} J D σ).obj.obj (op (n, V.unop)))
      ⊗ₜ[(systemRing.{c, v, max c v r} J B τ).obj.obj (op (n, V.unop)),
        (φ.hom.app (op (n, V.unop))).hom]
        (show M.val.obj (op (n, V.unop)) from
          M.val.map ((Prod.sectR n C).map f.unop).op x) := by
  let Q := (evaluation.{c, v, max c v r} J B τ n).obj M
  have ht := SheafOfModules.ScalarReductionProof.tensorRestriction_tmul
    (α n) Q f (1 : (D n).obj.obj U) x
  simp only [map_one] at ht
  refine (congrArg (fun z ↦ (e V).hom z) ht).trans ?_
  have hm : (Q.val.map f x : M.val.obj (op (n, V.unop))) =
      M.val.map ((Prod.sectR n C).map f.unop).op x := rfl
  exact (he V 1 (Q.val.map f x)).trans
      (congrArg (fun y : M.val.obj (op (n, V.unop)) ↦
        (1 : (systemRing.{c, v, max c v r} J D σ).obj.obj (op (n, V.unop)))
          ⊗ₜ[(systemRing.{c, v, max c v r} J B τ).obj.obj (op (n, V.unop)),
            (φ.hom.app (op (n, V.unop))).hom] y) hm)

/-- The left composite in tensor evaluation naturality has its generator value.
Source: Stacks Project, Section 03EK, restriction of pure tensors.
(blueprint: lem-sp-scalar-extension-evaluation-restriction-left).

Proof: restriction sends 1 tensor x to 1 tensor the restricted section x.
Apply the given pure-tensor formula for the sectionwise comparison before
or after restriction, respectively. Evaluation uses the same raw restriction. -/
theorem scalarExtension_evaluation_restriction_left
    {U V : Cᵒᵖ} (f : U ⟶ V)
    (x : ((evaluation.{c, v, max c v r} J B τ n).obj M).val.obj U) :
    (e V).hom
      ((SheafOfModules.changeOfRingsPresheaf.{v, c, max c v r} (α n)
        ((evaluation.{c, v, max c v r} J B τ n).obj M)).map f
          ((1 : (D n).obj.obj U) ⊗ₜ[(B n).obj.obj U,((α n).hom.app U).hom] x)) =
    (1 : (systemRing.{c, v, max c v r} J D σ).obj.obj (op (n, V.unop)))
      ⊗ₜ[(systemRing.{c, v, max c v r} J B τ).obj.obj (op (n, V.unop)),
        (φ.hom.app (op (n, V.unop))).hom]
        (show M.val.obj (op (n, V.unop)) from
          M.val.map ((Prod.sectR n C).map f.unop).op x) := by
  exact evaluatedTensorRestriction_left.{c, v, r} J B D τ σ α φ M n e he f x

end Construction

end WeilConjectures.SemilinearSections

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
