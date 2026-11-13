/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
/-! # The presheaf change-of-rings map

Construction part of the tensor change-of-rings presentation.
-/

@[expose] public section

universe u
open CategoryTheory Opposite MonoidalCategory
open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme.Modules
set_option hygiene false in
local notation "𝓡" S => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj S
set_option hygiene false in
local notation "𝓻" a => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map a
set_option maxHeartbeats 800000 in
-- Elaborating the nested scalar restrictions and tensor components needs extra heartbeats.
set_option backward.isDefEq.respectTransparency false in
/-- The presheaf change-of-rings map exists with its section formula.
(Stacks, Tag 01SB). -/
theorem exists_changeOfRings_tensor_presheaf_map (Y : Scheme.{u})
    (B C : Y.CommAlgebraSheaf) (φ : B ⟶ C)
    (P : SheafOfModules.{u} (𝓡 B.right)) :
    let P₀ := (SheafOfModules.restrictScalars (𝓻 B.hom)).obj P
    let T := (SheafOfModules.restrictScalars (𝓻 C.hom)).obj
      (SheafOfModules.changeOfRings.{u, u, u} φ.right P)
    letI := presheafMonoidalCategory Y
    ∃ (g : C.toModule.val ⊗ P₀.val ⟶ T.val),
      ∀ (W : Y.Opens) (c : C.right.obj.obj (op W)) (p : P.val.obj (op W)),
        g.app (op W) (c ⊗ₜ[Y.presheaf.obj (op W)] p) =
          (((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 C.right).obj)).unit.app
            (SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ.right P)).app (op W))
            (c ⊗ₜ[B.right.obj.obj (op W), (φ.right.hom.app (op W)).hom] p) := by
  classical
  dsimp only
  let P₀ := (SheafOfModules.restrictScalars (𝓻 B.hom)).obj P
  let Q := SheafOfModules.changeOfRingsPresheaf.{u, u, u} φ.right P
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 C.right).obj)).unit.app Q
  let T := (SheafOfModules.restrictScalars (𝓻 C.hom)).obj
    (SheafOfModules.changeOfRings.{u, u, u} φ.right P)
  let := presheafMonoidalCategory Y
  let a (W : Y.Opensᵒᵖ) : (C.toModule.val ⊗ P₀.val).obj W ⟶ T.val.obj W :=
    ModuleCat.MonoidalCategory.tensorLift
      (fun c p ↦ η.app W (c ⊗ₜ[B.right.obj.obj W, (φ.right.hom.app W).hom] p))
      (by
        intro c d p
        rw [TensorProduct.add_tmul]
        exact (η.app W).hom.map_add _ _)
      (by
        intro r c p
        change η.app W ((C.hom.hom.app W r * (show C.right.obj.obj W from c))
          ⊗ₜ[B.right.obj.obj W, (φ.right.hom.app W).hom] p) = C.hom.hom.app W r • _
        exact (η.app W).hom.map_smul (C.hom.hom.app W r)
          (c ⊗ₜ[B.right.obj.obj W, (φ.right.hom.app W).hom] p))
      (by
        intro c p q
        rw [TensorProduct.tmul_add]
        exact (η.app W).hom.map_add _ _)
      (by
        intro r c p
        change η.app W (c ⊗ₜ[B.right.obj.obj W, (φ.right.hom.app W).hom]
          (B.hom.hom.app W r • (show P.val.obj W from p))) = C.hom.hom.app W r • _
        let : Module (B.right.obj.obj W) (C.right.obj.obj W) :=
          Module.compHom (C.right.obj.obj W) (φ.right.hom.app W).hom
        change η.app W (c ⊗ₜ[B.right.obj.obj W]
          (B.hom.hom.app W r • (show P.val.obj W from p))) = _
        rw [TensorProduct.tmul_smul]
        have h : φ.right.hom.app W (B.hom.hom.app W r) = C.hom.hom.app W r := by
          have hw := congrArg (fun f ↦ f.hom.app W) (CategoryTheory.Under.w φ)
          exact congrArg (fun f ↦ f r) hw
        change η.app W ((φ.right.hom.app W (B.hom.hom.app W r) *
          (show C.right.obj.obj W from c)) ⊗ₜ[B.right.obj.obj W,
          (φ.right.hom.app W).hom] p) = _
        rw [h]
        exact (η.app W).hom.map_smul (C.hom.hom.app W r)
          (c ⊗ₜ[B.right.obj.obj W, (φ.right.hom.app W).hom] p))
  refine ⟨{ app := a, naturality := ?_ }, ?_⟩
  · intro U V f
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro c p
    change η.app V (C.right.obj.map f c ⊗ₜ[B.right.obj.obj V,
      (φ.right.hom.app V).hom] P.val.map f p) =
      T.val.map f (η.app U (c ⊗ₜ[B.right.obj.obj U, (φ.right.hom.app U).hom] p))
    have ht := Classical.choose_spec (SheafOfModules.exists_changeOfRingsMap φ.right P f) c p
    change Q.map f (c ⊗ₜ[B.right.obj.obj U, (φ.right.hom.app U).hom] p) = _ at ht
    rw [← ht]
    exact PresheafOfModules.naturality_apply η f _
  · intro W c p
    rfl
end AlgebraicGeometry.Scheme.Modules
