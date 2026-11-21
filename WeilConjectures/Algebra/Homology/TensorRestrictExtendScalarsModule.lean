/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

/-!
# Module tensor change of rings comparison

## References

* Stacks Project, More on Algebra, Tag 06Y1, proof.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory

namespace ModuleCat
/-- Restriction of scalars along `ρ` of `M ⊗ (extendScalars ρ).obj N` is isomorphic to
`(restrictScalars ρ).obj M ⊗ N`, naturally in both factors. -/
theorem exists_tensorRestrictExtend_module_natural
    {A B : Type u} [CommRing A] [CommRing B] (ρ : A →+* B) :
    ∃ e : ∀ (M : ModuleCat.{u} B) (N : ModuleCat.{u} A),
      (restrictScalars ρ).obj (M ⊗ (extendScalars ρ).obj N) ≅
        (restrictScalars ρ).obj M ⊗ N,
      ∀ (M M' : ModuleCat.{u} B) (N N' : ModuleCat.{u} A)
        (f : M ⟶ M') (g : N ⟶ N'),
        (restrictScalars ρ).map (f ⊗ₘ (extendScalars ρ).map g) ≫ (e M' N').hom =
          (e M N).hom ≫ ((restrictScalars ρ).map f ⊗ₘ g) := by
  let : Algebra A B := ρ.toAlgebra
  let e (M : ModuleCat.{u} B) (N : ModuleCat.{u} A) :
      (restrictScalars ρ).obj (M ⊗ (extendScalars ρ).obj N) ≅
        (restrictScalars ρ).obj M ⊗ N := by
    let : Module A M := Module.compHom M ρ
    let : IsScalarTower A B M := IsScalarTower.of_algebraMap_smul (fun a m ↦ rfl)
    exact (TensorProduct.AlgebraTensorModule.cancelBaseChange A B B M N).restrictScalars A
      |>.toModuleIso
  refine ⟨e, ?_⟩
  intro M M' N N' f g
  let : Module A M := Module.compHom M ρ
  let : Module A M' := Module.compHom M' ρ
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul m x =>
    change TensorProduct A B N at x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy =>
      simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hx hy
    | tmul b n =>
      change (b • f m) ⊗ₜ[A] g n = f (b • m) ⊗ₜ[A] g n
      rw [f.hom.map_smul]
end ModuleCat
