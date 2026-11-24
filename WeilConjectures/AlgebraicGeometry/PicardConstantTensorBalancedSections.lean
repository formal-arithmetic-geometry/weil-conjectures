/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PicardConstantSectionsTensor
import WeilConjectures.AlgebraicGeometry.PicardConstantScalarExtensionSections

/-! # Balanced sections of scalar-extended constant tensor coefficients

## References

* Stacks Project, Varieties, Tag 0BED.
-/

public section
universe w
open CategoryTheory Opposite
open scoped TensorProduct ChangeOfRings
namespace AlgebraicGeometry.Scheme.Modules
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Scalar extension followed by tensoring with `G` has the usual balanced sections. -/
noncomputable def picardConstantTensorBalancedSections
    (k : Type w) [Field k] (Y : Scheme.{w})
    (g : Y ⟶ Spec (CommRingCat.of k)) (M : ModuleCat.{w} k) (G : Y.Modules)
    (V : Y.Opens) :
    (picardConstantSectionsTensor k Y g M G).obj (op V) ≃+ (M ⊗[k] scalarObj g G (op V)) := by
  let q := picardConstantScalarExtensionSections k Y g M
  let : Algebra k Γ(Y, V) := (scalarMap g V).toAlgebra
  let : Module k (G.val.obj (op V)) := Module.compHom _ (scalarMap g V)
  let : IsScalarTower k Γ(Y, V) (G.val.obj (op V)) :=
    IsScalarTower.of_algebraMap_smul (fun a t ↦ rfl)
  exact (TensorProduct.congr (q V).symm (LinearEquiv.refl _ _)).toAddEquiv.trans
    ((TensorProduct.comm Γ(Y, V) _ _).toAddEquiv.trans
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange
        k Γ(Y, V) Γ(Y, V) (G.val.obj (op V)) M).toAddEquiv.trans
          (TensorProduct.comm k _ _).toAddEquiv))

private theorem picardConstantTensorBalancedSections_tmul
    (k : Type w) [Field k] (Y : Scheme.{w})
    (g : Y ⟶ Spec (CommRingCat.of k)) (M : ModuleCat.{w} k) (G : Y.Modules)
    (V : Y.Opens) (a : Γ(Y, V)) (s : M) (t : G.val.obj (op V)) :
    picardConstantTensorBalancedSections k Y g M G V
        ((picardConstantScalarExtensionSections k Y g M V
          (a ⊗ₜ[k, scalarMap g V] s)) ⊗ₜ[Γ(Y, V)] t) =
      s ⊗ₜ[k] (show scalarObj g G (op V) from a • t) := by
  let : Algebra k Γ(Y, V) := (scalarMap g V).toAlgebra
  let : Module k (G.val.obj (op V)) := Module.compHom _ (scalarMap g V)
  let : IsScalarTower k Γ(Y, V) (G.val.obj (op V)) :=
    IsScalarTower.of_algebraMap_smul (fun a t ↦ rfl)
  simp [picardConstantTensorBalancedSections]
  rfl

/-- The balanced identification is linear for the action of `O_Y(V)` on the second factor. -/
theorem picardConstantTensorBalancedSections_smul
    (k : Type w) [Field k] (Y : Scheme.{w})
    (g : Y ⟶ Spec (CommRingCat.of k)) (M : ModuleCat.{w} k) (G : Y.Modules)
    (V : Y.Opens) (a : Γ(Y, V)) (s : M) (t : scalarObj g G (op V)) :
    picardConstantTensorBalancedSections k Y g M G V
        (a • (picardConstantTensorBalancedSections k Y g M G V).symm (s ⊗ₜ[k] t)) =
      s ⊗ₜ[k] (show scalarObj g G (op V) from a • (show G.val.obj (op V) from t)) := by
  classical
  let tmul (V : Y.Opens) (a : Γ(Y, V)) (s : M) :
      (ModuleCat.extendScalars (scalarMap g V)).obj M := by
    let : Module k Γ(Y, V) := Module.compHom _ (scalarMap g V)
    exact TensorProduct.tmul k a s
  let e := picardConstantTensorBalancedSections k Y g M G
  let q := picardConstantScalarExtensionSections k Y g M
  have he := picardConstantTensorBalancedSections_tmul k Y g M G
  have hi : (e V).symm (s ⊗ₜ[k] t) =
      (q V (tmul V 1 s)) ⊗ₜ[Γ(Y, V)]
        (show G.val.obj (op V) from t) := by
    apply (e V).injective
    rw [AddEquiv.apply_symm_apply]
    refine Eq.symm ((he V 1 s t).trans ?_)
    simp
  rw [hi]
  change e V (a • (_ ⊗ₜ[Γ(Y, V)] _)) = _
  rw [← TensorProduct.tmul_smul]
  simpa only [one_smul] using he V 1 s (a • (show G.val.obj (op V) from t))

/-- The balanced identification commutes with restriction. -/
theorem picardConstantTensorBalancedSections_map
    (k : Type w) [Field k] (Y : Scheme.{w})
    (g : Y ⟶ Spec (CommRingCat.of k)) (M : ModuleCat.{w} k) (G : Y.Modules)
    {U V : Y.Opensᵒᵖ} (i : U ⟶ V)
    (x : (picardConstantSectionsTensor k Y g M G).obj U) :
    picardConstantTensorBalancedSections k Y g M G V.unop
        ((picardConstantSectionsTensor k Y g M G).map i x) =
      ((scalarPresheaf g G ⋙ MonoidalCategory.tensorLeft M).map i)
        (picardConstantTensorBalancedSections k Y g M G U.unop x) := by
  classical
  let tmul (V : Y.Opens) (a : Γ(Y, V)) (s : M) :
      (ModuleCat.extendScalars (scalarMap g V)).obj M := by
    let : Module k Γ(Y, V) := Module.compHom _ (scalarMap g V)
    exact TensorProduct.tmul k a s
  let e := picardConstantTensorBalancedSections k Y g M G
  let q := picardConstantScalarExtensionSections k Y g M
  have hq := @picardConstantScalarExtensionSections_map k _ Y g M
  have he := picardConstantTensorBalancedSections_tmul k Y g M G
  let P := (PresheafOfModules.pullback (picardConstantRingMap k Y g)).obj
    (picardConstantVector k Y M)
  change e V.unop ((MonoidalCategory.tensorObj P G.val).map i x) = _
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul p t =>
    obtain ⟨z, rfl⟩ := (q U.unop).surjective p
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' =>
      simpa only [map_add, TensorProduct.add_tmul] using congrArg₂ (· + ·) hz hz'
    | tmul a s =>
      change e V.unop (P.map i (q U.unop (tmul U.unop a s))
        ⊗ₜ[Γ(Y, V.unop)] G.val.map i t) = _
      rw [hq, he]
      change _ = ((scalarPresheaf g G ⋙ MonoidalCategory.tensorLeft M).map i)
        (e U.unop ((q U.unop (tmul U.unop a s))
          ⊗ₜ[Γ(Y, U.unop)] t))
      rw [he]
      change s ⊗ₜ[k] (show scalarObj g G V from
          (Y.presheaf.map i a) • (show G.val.obj V from G.val.map i t)) =
        s ⊗ₜ[k] (show scalarObj g G V from
          G.val.map i ((show Γ(Y, U.unop) from a) • t))
      rw [G.val.map_smul]
      rfl


end AlgebraicGeometry.Scheme.Modules
