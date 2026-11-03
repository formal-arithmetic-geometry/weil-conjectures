/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Properties of objects and five-term exact sequences

Let `P` be a property of objects of an abelian category which is closed under kernels,
cokernels and extensions. In an exact sequence `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₄ ⟶ X₅`, if `P` holds for the
four outer terms, then it holds for `X₃`, since `X₃` is an extension of `ker (X₄ ⟶ X₅)` by
`coker (X₁ ⟶ X₂)` (`CategoryTheory.ObjectProperty.prop_X₃_of_exact`). We also allow the exact
sequence to live in another abelian category, into which the category of `P` embeds by a fully
faithful exact functor (`CategoryTheory.ObjectProperty.prop_X₃_of_exact_of_fullyFaithful`).
-/

@[expose] public section

namespace CategoryTheory.ObjectProperty

open Limits

variable {C : Type*} [Category* C] [Abelian C]

/-- Let `P` be closed under kernels, cokernels and extensions. If `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₄ ⟶ X₅`
is exact at `X₂`, `X₃` and `X₄`, and `P` holds for `X₁`, `X₂`, `X₄` and `X₅`, then `P` holds
for `X₃`. -/
theorem prop_X₃_of_exact (P : ObjectProperty C)
    (hker : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), P X → P Y → P (kernel f))
    (hcoker : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), P X → P Y → P (cokernel f))
    (hext : ∀ S : ShortComplex C, S.ShortExact → P S.X₁ → P S.X₃ → P S.X₂)
    {X₁ X₂ X₃ X₄ X₅ : C} {f₁ : X₁ ⟶ X₂} {f₂ : X₂ ⟶ X₃} {f₃ : X₃ ⟶ X₄} {f₄ : X₄ ⟶ X₅}
    {w₁ : f₁ ≫ f₂ = 0} {w₂ : f₂ ≫ f₃ = 0} {w₃ : f₃ ≫ f₄ = 0}
    (h₁ : (ShortComplex.mk f₁ f₂ w₁).Exact) (h₂ : (ShortComplex.mk f₂ f₃ w₂).Exact)
    (h₃ : (ShortComplex.mk f₃ f₄ w₃).Exact)
    (hX₁ : P X₁) (hX₂ : P X₂) (hX₄ : P X₄) (hX₅ : P X₅) : P X₃ := by
  have : Mono (cokernel.desc f₁ f₂ w₁) := h₁.mono_cokernelDesc
  have : Epi (kernel.lift f₄ f₃ w₃) := h₃.epi_kernelLift
  have w : cokernel.desc f₁ f₂ w₁ ≫ kernel.lift f₄ f₃ w₃ = 0 := by
    ext
    simp [w₂]
  let S := ShortComplex.mk _ _ w
  let S' := ShortComplex.mk (cokernel.desc f₁ f₂ w₁) f₃ (by ext; simp [w₂])
  let φ : ShortComplex.mk f₂ f₃ w₂ ⟶ S' :=
    { τ₁ := cokernel.π f₁, τ₂ := 𝟙 _, τ₃ := 𝟙 _ }
  let ψ : S ⟶ S' :=
    { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := kernel.ι f₄ }
  have hS : S.Exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ).2
    ((ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 h₂)
  exact hext S { exact := hS } (hcoker f₁ hX₁ hX₂) (hker f₄ hX₄ hX₅)

variable {D : Type*} [Category* D] [Abelian D]

/-- Variant of `CategoryTheory.ObjectProperty.prop_X₃_of_exact` in which the exact sequence
lives in an abelian category `D`, and its terms are identified with the images of objects of
`C` under a fully faithful exact functor `F : C ⥤ D`. -/
theorem prop_X₃_of_exact_of_fullyFaithful (F : C ⥤ D) [F.Full] [F.Faithful] [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (P : ObjectProperty C)
    (hker : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), P X → P Y → P (kernel f))
    (hcoker : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), P X → P Y → P (cokernel f))
    (hext : ∀ S : ShortComplex C, S.ShortExact → P S.X₁ → P S.X₃ → P S.X₂)
    {Y₁ Y₂ Y₃ Y₄ Y₅ : D} {f₁ : Y₁ ⟶ Y₂} {f₂ : Y₂ ⟶ Y₃} {f₃ : Y₃ ⟶ Y₄} {f₄ : Y₄ ⟶ Y₅}
    {w₁ : f₁ ≫ f₂ = 0} {w₂ : f₂ ≫ f₃ = 0} {w₃ : f₃ ≫ f₄ = 0}
    (h₁ : (ShortComplex.mk f₁ f₂ w₁).Exact) (h₂ : (ShortComplex.mk f₂ f₃ w₂).Exact)
    (h₃ : (ShortComplex.mk f₃ f₄ w₃).Exact)
    {X₁ X₂ X₃ X₄ X₅ : C} (e₁ : Y₁ ≅ F.obj X₁) (e₂ : Y₂ ≅ F.obj X₂) (e₃ : Y₃ ≅ F.obj X₃)
    (e₄ : Y₄ ≅ F.obj X₄) (e₅ : Y₅ ≅ F.obj X₅)
    (hX₁ : P X₁) (hX₂ : P X₂) (hX₄ : P X₄) (hX₅ : P X₅) : P X₃ := by
  let g₁ := F.preimage (e₁.inv ≫ f₁ ≫ e₂.hom)
  let g₂ := F.preimage (e₂.inv ≫ f₂ ≫ e₃.hom)
  let g₃ := F.preimage (e₃.inv ≫ f₃ ≫ e₄.hom)
  let g₄ := F.preimage (e₄.inv ≫ f₄ ≫ e₅.hom)
  have v₁ : g₁ ≫ g₂ = 0 := F.map_injective (by simp [g₁, g₂, reassoc_of% w₁])
  have v₂ : g₂ ≫ g₃ = 0 := F.map_injective (by simp [g₂, g₃, reassoc_of% w₂])
  have v₃ : g₃ ≫ g₄ = 0 := F.map_injective (by simp [g₃, g₄, reassoc_of% w₃])
  have hex {Z₁ Z₂ Z₃ : C} {W₁ W₂ W₃ : D} (a : W₁ ⟶ W₂) (b : W₂ ⟶ W₃) (wab : a ≫ b = 0)
      (k₁ : W₁ ≅ F.obj Z₁) (k₂ : W₂ ≅ F.obj Z₂) (k₃ : W₃ ≅ F.obj Z₃)
      (hab : (ShortComplex.mk a b wab).Exact) (wg : F.preimage (k₁.inv ≫ a ≫ k₂.hom) ≫
        F.preimage (k₂.inv ≫ b ≫ k₃.hom) = 0) :
      (ShortComplex.mk _ _ wg).Exact := by
    rw [← ShortComplex.exact_map_iff_of_faithful _ F]
    exact ShortComplex.exact_of_iso (ShortComplex.isoMk k₁ k₂ k₃ (by simp) (by simp)) hab
  exact prop_X₃_of_exact P hker hcoker hext (hex _ _ _ e₁ e₂ e₃ h₁ v₁)
    (hex _ _ _ e₂ e₃ e₄ h₂ v₂) (hex _ _ _ e₃ e₄ e₅ h₃ v₃) hX₁ hX₂ hX₄ hX₅

end CategoryTheory.ObjectProperty
