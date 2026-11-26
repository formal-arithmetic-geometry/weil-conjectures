/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Etale.Basic
import WeilConjectures.RingTheory.SmoothProductAlgebra

/-!
# Smoothness over a product ring

If `R₁ → A₁` and `R₂ → A₂` are smooth, then so is `R₁ × R₂ → A₁ × A₂`.

## References

* [Stacks, Tag 0GIF]
* [Stacks, Tag 00TD]
-/

@[expose] public section

universe u₁ u₂ v₁ v₂

namespace Algebra

/-- Smooth ring maps on two factors induce a smooth map on product rings. -/
theorem smooth_over_product_ring
    (R₁ : Type u₁) (R₂ : Type u₂) (A₁ : Type v₁) (A₂ : Type v₂)
    [CommRing R₁] [CommRing R₂] [CommRing A₁] [CommRing A₂]
    (φ₁ : R₁ →+* A₁) (φ₂ : R₂ →+* A₂)
    (h₁ : @Algebra.Smooth R₁ _ A₁ _ (RingHom.toAlgebra φ₁))
    (h₂ : @Algebra.Smooth R₂ _ A₂ _ (RingHom.toAlgebra φ₂)) :
    @Algebra.Smooth (R₁ × R₂) _ (A₁ × A₂) _ (RingHom.toAlgebra (RingHom.prodMap φ₁ φ₂)) := by
  let : Algebra R₁ A₁ := φ₁.toAlgebra
  let : Algebra R₂ A₂ := φ₂.toAlgebra
  let : Smooth R₁ A₁ := h₁
  let : Smooth R₂ A₂ := h₂
  let : Algebra (R₁ × R₂) R₁ := (RingHom.fst R₁ R₂).toAlgebra
  let : Algebra (R₁ × R₂) R₂ := (RingHom.snd R₁ R₂).toAlgebra
  let : Algebra (R₁ × R₂) A₁ := (φ₁.comp (RingHom.fst R₁ R₂)).toAlgebra
  let : Algebra (R₁ × R₂) A₂ := (φ₂.comp (RingHom.snd R₁ R₂)).toAlgebra
  let : IsScalarTower (R₁ × R₂) R₁ A₁ := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower (R₁ × R₂) R₂ A₂ := IsScalarTower.of_algebraMap_eq' rfl
  let : Smooth (R₁ × R₂) A₁ := Smooth.comp (R₁ × R₂) R₁ A₁
  let : Smooth (R₁ × R₂) A₂ := Smooth.comp (R₁ × R₂) R₂ A₂
  exact Smooth.prod (R₁ × R₂) A₁ A₂

end Algebra
