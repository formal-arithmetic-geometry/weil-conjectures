/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P5
-/
module

public import Sheaf.Paper.SemilinearSystemModels
import Sheaf.Paper.ScalarExtensionEvaluationRestrictionLeft
import Sheaf.Paper.ScalarExtensionEvaluationRestrictionRight

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

/-- Sectionwise pure-tensor comparisons commute with restriction.
Source: Stacks Project, Section 03EK, the tensor presheaf restriction maps.
(blueprint: lem-sp-scalar-extension-evaluation-naturality).

Proof: extension-of-scalars homomorphisms are determined on 1 tensor x. The
finite-level restriction and the system restriction both send this generator to
1 tensor the restriction of x. Apply he at the source and target. -/
theorem scalarExtension_evaluation_naturality {U V : Cᵒᵖ} (f : U ⟶ V) :
    (SheafOfModules.changeOfRingsPresheaf.{v, c, max c v r} (α n)
      ((evaluation.{c, v, max c v r} J B τ n).obj M)).map f ≫
        (ModuleCat.restrictScalars ((ring.{c, v, max c v r} J (D n)).obj.map f).hom).map
          (e V).hom =
    (e U).hom ≫
      ((PresheafOfModules.pushforward (F := Prod.sectR n C)
        (eqToHom (evaluation_ring.{c, v, max c v r} J D σ n).symm).hom).obj
          (SheafOfModules.changeOfRingsPresheaf.{v, c, max c v r} φ M)).map f := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  exact (scalarExtension_evaluation_restriction_left.{c, v, r} J B D τ σ α φ M n e he f x).trans
    (scalarExtension_evaluation_restriction_right.{c, v, r} J B D τ σ α φ M n e he f x).symm

end Construction

end WeilConjectures.SemilinearSections

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
