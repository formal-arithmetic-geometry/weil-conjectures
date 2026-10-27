/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P8
-/
module

public import Sheaf.CategoryTheory.Sites.OrientedProductUniversal
import Mathlib.CategoryTheory.Equivalence

/-! # Comparison of universal oriented cones

Source: ILO Exposé XI Theorem 1.4 and Definition 1.7.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace CategoryTheory.OrientedProduct

private def identity (P : Type (u + 1)) [Category.{u} P] : GeometricMorphism P P where
  inverse := 𝟭 P
  direct := 𝟭 P
  adj := Adjunction.id
  leftExact := inferInstance

variable {X Y S P Q R : Type (u + 1)}
  [Category.{u} X] [Category.{u} Y] [Category.{u} S]
  [Category.{u} P] [Category.{u} Q] [Category.{u} R]
  (f : GeometricMorphism X S) (g : GeometricMorphism Y S)
  (p₁ : GeometricMorphism P X) (p₂ : GeometricMorphism P Y)
  (τ : (p₂.comp g).direct ⟶ (p₁.comp f).direct)
  (q₁ : GeometricMorphism Q X) (q₂ : GeometricMorphism Q Y)
  (σ : (q₂.comp g).direct ⟶ (q₁.comp f).direct)

private theorem paste_comp
    (h : GeometricMorphism Q P)
    (α : (h.comp p₁).direct ≅ q₁.direct) (β : (h.comp p₂).direct ≅ q₂.direct)
    (hh : paste f g p₁ p₂ τ h q₁ q₂ α β = σ)
    (k : GeometricMorphism R Q)
    (r₁ : GeometricMorphism R X) (r₂ : GeometricMorphism R Y)
    (ρ : (r₂.comp g).direct ⟶ (r₁.comp f).direct)
    (a : (k.comp q₁).direct ≅ r₁.direct) (b : (k.comp q₂).direct ≅ r₂.direct)
    (hk : paste f g q₁ q₂ σ k r₁ r₂ a b = ρ) :
    paste f g p₁ p₂ τ (k.comp h) r₁ r₂
      (Functor.associator k.direct h.direct p₁.direct ≪≫
        Functor.isoWhiskerLeft k.direct α ≪≫ a)
      (Functor.associator k.direct h.direct p₂.direct ≪≫
        Functor.isoWhiskerLeft k.direct β ≪≫ b) = ρ := by
  rw [← hk, ← hh]
  ext Z
  simp [paste, GeometricMorphism.comp, Category.assoc]

/-- Two universal oriented cones are equivalent by their compatible comparison morphism.

Source: ILO Exposé XI Theorem 1.4 and Definition 1.7
(blueprint: lem-trf-oriented-universal-comparison).

Apply the two universal properties to the opposite cones to obtain comparison morphisms.
The composites and the identity morphisms are compatible lifts of the same cones.
Uniqueness therefore identifies both composites with identities, proving that either
comparison is an equivalence. The uniqueness assertion is the original universal property.
-/
theorem universalComparison
    (hP : IsGrothendieckTopos.{u} P) (hQ : IsGrothendieckTopos.{u} Q)
    (hp : IsUniversal.{u, u + 1, u} f g p₁ p₂ τ)
    (hq : IsUniversal.{u, u + 1, u} f g q₁ q₂ σ) :
    ∃ (h : GeometricMorphism Q P)
      (α : (h.comp p₁).direct ≅ q₁.direct) (β : (h.comp p₂).direct ≅ q₂.direct),
      paste f g p₁ p₂ τ h q₁ q₂ α β = σ ∧ h.direct.IsEquivalence ∧
      ∀ (h' : GeometricMorphism Q P)
        (α' : (h'.comp p₁).direct ≅ q₁.direct) (β' : (h'.comp p₂).direct ≅ q₂.direct),
        paste f g p₁ p₂ τ h' q₁ q₂ α' β' = σ →
        ∃! γ : h.direct ≅ h'.direct,
          Functor.isoWhiskerRight γ p₁.direct ≪≫ α' = α ∧
          Functor.isoWhiskerRight γ p₂.direct ≪≫ β' = β := by
  obtain ⟨h, α, β, hh, hu⟩ := hp Q hQ q₁ q₂ σ
  obtain ⟨k, a, b, hk, _⟩ := hq P hP p₁ p₂ τ
  have hidP : paste f g p₁ p₂ τ (identity P) p₁ p₂
      (Functor.leftUnitor p₁.direct) (Functor.leftUnitor p₂.direct) = τ := by
    ext Z
    simp [paste, identity, GeometricMorphism.comp]
  have hidQ : paste f g q₁ q₂ σ (identity Q) q₁ q₂
      (Functor.leftUnitor q₁.direct) (Functor.leftUnitor q₂.direct) = σ := by
    ext Z
    simp [paste, identity, GeometricMorphism.comp]
  have hkh := paste_comp f g p₁ p₂ τ q₁ q₂ σ h α β hh k p₁ p₂ τ a b hk
  have hhk := paste_comp f g q₁ q₂ σ p₁ p₂ τ k a b hk h q₁ q₂ σ α β hh
  obtain ⟨l, l₁, l₂, _, hl⟩ := hp P hP p₁ p₂ τ
  obtain ⟨i, _, _⟩ := hl (k.comp h) _ _ hkh
  obtain ⟨j, _, _⟩ := hl (identity P) _ _ hidP
  let ε : k.direct ⋙ h.direct ≅ 𝟭 P := i.symm ≪≫ j
  obtain ⟨m, m₁, m₂, _, hm⟩ := hq Q hQ q₁ q₂ σ
  obtain ⟨i', _, _⟩ := hm (h.comp k) _ _ hhk
  obtain ⟨j', _, _⟩ := hm (identity Q) _ _ hidQ
  let η : 𝟭 Q ≅ h.direct ⋙ k.direct := (i'.symm ≪≫ j').symm
  have : h.direct.IsEquivalence := Functor.IsEquivalence.mk' k.direct η ε
  exact ⟨h, α, β, hh, this, hu⟩

end CategoryTheory.OrientedProduct
