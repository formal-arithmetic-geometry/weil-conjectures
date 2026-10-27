/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P5
-/
module

public import Sheaf.Paper.SemilinearSystemModels

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

@[irreducible] private def extensionTransport {R S : Type r} [CommRing R] [CommRing S]
    (f g : R →+* S) (hf : f = g) (p : R →+* R) (hp : p = RingHom.id R)
    (q : S →+* S) (hq : q = RingHom.id S) (M : ModuleCat.{r} R) :
    (ModuleCat.extendScalars f).obj ((ModuleCat.restrictScalars p).obj M) ≅
      (ModuleCat.restrictScalars q).obj ((ModuleCat.extendScalars g).obj M) := by
  subst g
  subst p
  subst q
  exact Iso.refl _

private theorem extensionTransport_pure {R S : Type r} [CommRing R] [CommRing S]
    (f g : R →+* S) (hf : f = g) (p : R →+* R) (hp : p = RingHom.id R)
    (q : S →+* S) (hq : q = RingHom.id S) (M : ModuleCat.{r} R) (a : S) (x : M) :
    (extensionTransport f g hf p hp q hq M).hom
      (a ⊗ₜ[R, f] (show (ModuleCat.restrictScalars p).obj M from x)) =
      a ⊗ₜ[R, g] x := by
  subst g
  subst p
  subst q
  unfold extensionTransport
  rfl

section Construction
variable {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
  (J : GrothendieckTopology C)
  (B D : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n, B (n + 1) ⟶ B n) (σ : ∀ n, D (n + 1) ⟶ D n)
  (α : ∀ n, B n ⟶ D n)
  (φ : systemRing.{c, v, max c v r} J B τ ⟶ systemRing.{c, v, max c v r} J D σ)
  (hφ : ∀ (n : ℕ) (U : Cᵒᵖ), φ.hom.app (op (n, U.unop)) = (α n).hom.app U)

private theorem evaluationRingHom_id (n : ℕ) (U : Cᵒᵖ) :
    (eqToHom (evaluation_ring.{c, v, max c v r} J B τ n).symm).hom.app U = 𝟙 _ := by
  rw [ObjectProperty.eqToHom_hom, eqToHom_app]
  rfl

include hφ

private theorem systemMap_app (n : ℕ) (U : Cᵒᵖ) :
    φ.hom.app (op (n, U.unop)) = (α n).hom.app U :=
  hφ n U

@[irreducible] private def evaluationExtensionPresheafObjIso
    (M : Systems.{c, v, max c v r} J B τ) (n : ℕ) (U : Cᵒᵖ) :
    (SheafOfModules.changeOfRingsPresheaf.{v, c, max c v r}
      (α n) ((evaluation.{c, v, max c v r} J B τ n).obj M)).obj U ≅
      ((PresheafOfModules.pushforward (F := Prod.sectR n C)
        (eqToHom (evaluation_ring.{c, v, max c v r} J D σ n).symm).hom).obj
          (SheafOfModules.changeOfRingsPresheaf.{v, c, max c v r}
            φ M)).obj U := by
  exact extensionTransport ((α n).hom.app U).hom
    (φ.hom.app (op (n, U.unop))).hom
    (congrArg CommRingCat.Hom.hom (systemMap_app.{c, v, r} J B D τ σ α φ hφ n U).symm)
    ((eqToHom (evaluation_ring.{c, v, max c v r} J B τ n).symm).hom.app U).hom
    (congrArg RingCat.Hom.hom (evaluationRingHom_id.{c, v, r} J B τ n U))
    ((eqToHom (evaluation_ring.{c, v, max c v r} J D σ n).symm).hom.app U).hom
    (congrArg RingCat.Hom.hom (evaluationRingHom_id.{c, v, r} J D σ n U))
    (M.val.obj (op (n, U.unop)))

/-- The sectionwise comparison for evaluated tensor products fixes pure tensors.
Source: Stacks Project, Section 03EK, the sectionwise construction of scalar extension.

Proof: both section rings are unchanged by evaluation. The coefficient morphism has
component alpha, and the two evaluation transports are the identity ring maps.
After substituting these equalities, both extension modules and the map are identical. -/
private theorem evaluationExtensionPresheafObjIso_pure
    (M : Systems.{c, v, max c v r} J B τ) (n : ℕ) (U : Cᵒᵖ)
    (a : (D n).obj.obj U) (x : M.val.obj (op (n, U.unop))) :
    (evaluationExtensionPresheafObjIso.{c, v, r} J B D τ σ α φ hφ M n U).hom
        (a ⊗ₜ[(B n).obj.obj U,((α n).hom.app U).hom] x) =
      (show (systemRing.{c, v, max c v r} J D σ).obj.obj (op (n, U.unop)) from a)
        ⊗ₜ[(B n).obj.obj U,
        (φ.hom.app (op (n, U.unop))).hom] x := by
  unfold evaluationExtensionPresheafObjIso
  exact extensionTransport_pure ((α n).hom.app U).hom
    (φ.hom.app (op (n, U.unop))).hom
    (congrArg CommRingCat.Hom.hom (systemMap_app.{c, v, r} J B D τ σ α φ hφ n U).symm)
    ((eqToHom (evaluation_ring.{c, v, max c v r} J B τ n).symm).hom.app U).hom
    (congrArg RingCat.Hom.hom (evaluationRingHom_id.{c, v, r} J B τ n U))
    ((eqToHom (evaluation_ring.{c, v, max c v r} J D σ n).symm).hom.app U).hom
    (congrArg RingCat.Hom.hom (evaluationRingHom_id.{c, v, r} J D σ n U))
    (M.val.obj (op (n, U.unop))) a x

/-- Evaluation identifies sectionwise scalar extensions, fixing pure tensors.
Source: Stacks Project, Section 03EK, the sectionwise construction of scalar extension.
(blueprint: lem-sp-scalar-extension-evaluation-objects).

Proof: the evaluation coefficient transports are identity ring maps, and phi has
component alpha. Substitute these equalities to identify the two tensor modules.
The resulting identity isomorphism fixes every pure tensor. -/
theorem scalarExtension_evaluation_objects
    (M : Systems.{c, v, max c v r} J B τ) (n : ℕ) :
    ∃ e : ∀ U : Cᵒᵖ,
    (SheafOfModules.changeOfRingsPresheaf.{v, c, max c v r}
      (α n) ((evaluation.{c, v, max c v r} J B τ n).obj M)).obj U ≅
      ((PresheafOfModules.pushforward (F := Prod.sectR n C)
        (eqToHom (evaluation_ring.{c, v, max c v r} J D σ n).symm).hom).obj
          (SheafOfModules.changeOfRingsPresheaf.{v, c, max c v r}
            φ M)).obj U,
      ∀ (U : Cᵒᵖ) (a : (D n).obj.obj U) (x : M.val.obj (op (n, U.unop))),
        (e U).hom (a ⊗ₜ[(B n).obj.obj U,((α n).hom.app U).hom] x) =
          (show (systemRing.{c, v, max c v r} J D σ).obj.obj (op (n, U.unop)) from a)
            ⊗ₜ[(B n).obj.obj U,(φ.hom.app (op (n, U.unop))).hom] x := by
  exact ⟨evaluationExtensionPresheafObjIso.{c, v, r} J B D τ σ α φ hφ M n,
    evaluationExtensionPresheafObjIso_pure.{c, v, r} J B D τ σ α φ hφ M n⟩

end Construction

end WeilConjectures.SemilinearSections

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
