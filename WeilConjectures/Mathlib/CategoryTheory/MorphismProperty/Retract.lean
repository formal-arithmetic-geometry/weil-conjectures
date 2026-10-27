/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.MorphismProperty.Retract

/-!

# Retracts of isomorphisms along split monomorphisms

A morphism `x` sitting in a commutative square `x ≫ a = w ≫ π` whose horizontal maps `w`, `a` are
split monomorphisms, with retractions whose idempotents are compatible with `π`, is a retract of
`π` (`CategoryTheory.retractArrowOfCompEqOfRetraction`); since isomorphisms are stable under
retracts, `x` is invertible if `π` is (`CategoryTheory.isIso_of_comp_eq_of_retraction`).

## Main statements

* `CategoryTheory.isIso_of_comp_eq_of_retraction`: the abstract retract argument.
* `CategoryTheory.IsSquareRetract.isIso`: the retract argument for a square
  `x ≫ a = δ ≫ t ≫ π` with `δ` and `π` invertible.
* `CategoryTheory.IsTensorRetract.isSquareRetract`: in a monoidal category, a retraction of `u₁`
  and an invertible `u₂` give a retraction of `u₁ ⊗ u₂`.

-/

@[expose] public section

namespace CategoryTheory

variable {C : Type*} [Category C]

section

variable {U V U' V' : C} {x : U ⟶ V} {a : V ⟶ V'} {w : U ⟶ U'} {π : U' ⟶ V'} {ρ : V' ⟶ V}
  {w' : U' ⟶ U}

/-- **A morphism is a retract of `π` along split monomorphisms**: given the commutative square
`x ≫ a = w ≫ π` and retractions `w'` of `w` and `ρ` of `a` whose idempotents are compatible with
`π` (`w' ≫ w ≫ π = π ≫ ρ ≫ a`), the diagram
```
  U --w--> U' --w'--> U
  |        |          |
  x        π          x
  v        v          v
  V --a--> V' --ρ---> V
```
commutes, so that `x` is a retract of `π`. -/
def retractArrowOfCompEqOfRetraction (ha : a ≫ ρ = 𝟙 V) (hw : w ≫ w' = 𝟙 U)
    (hsq : x ≫ a = w ≫ π) (hc : w' ≫ w ≫ π = π ≫ ρ ≫ a) : RetractArrow x π where
  i := Arrow.homMk w a hsq.symm
  r := Arrow.homMk w' ρ (by
    have hx : x = w ≫ π ≫ ρ := by rw [← reassoc_of% hsq, ha, Category.comp_id]
    simp only [Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom]
    rw [hx, reassoc_of% hc, ha, Category.comp_id])
  retract := by ext <;> simp [hw, ha]

/-- **A retract of an isomorphism along split monomorphisms is an isomorphism**: in the
commutative diagram
```
  U --w--> U' --w'--> U
  |        |          |
  x        π          x
  v        v          v
  V --a--> V' --ρ---> V
```
with `w ≫ w' = 𝟙`, `a ≫ ρ = 𝟙` and `π` invertible, the morphism `x` is invertible. The
commutativity of the right square follows from that of the left one and the compatibility
`w' ≫ w ≫ π = π ≫ ρ ≫ a` of the idempotents with `π`. -/
lemma isIso_of_comp_eq_of_retraction [IsIso π] (ha : a ≫ ρ = 𝟙 V) (hw : w ≫ w' = 𝟙 U)
    (hsq : x ≫ a = w ≫ π) (hc : w' ≫ w ≫ π = π ≫ ρ ≫ a) : IsIso x :=
  (MorphismProperty.isomorphisms C).of_retract
    (retractArrowOfCompEqOfRetraction ha hw hsq hc) (inferInstanceAs (IsIso π))

end

/-- A *retract structure* on a commutative square `x ≫ a = δ ≫ t ≫ π`
```
  U --δ--> S --t--> T
  |                 |
  x                 π
  v                 v
  V ------a-------> V'
```
consists of retractions `t'` of `t` and `ρ` of `a` such that `π` carries the idempotent `t' ≫ t`
to the idempotent `ρ ≫ a`. -/
def IsSquareRetract {U V V' S T : C} {x : U ⟶ V} {a : V ⟶ V'} {δ : U ⟶ S} {t : S ⟶ T}
    {π : T ⟶ V'} (_ : x ≫ a = δ ≫ t ≫ π) : Prop :=
  ∃ (t' : T ⟶ S) (ρ : V' ⟶ V), t ≫ t' = 𝟙 S ∧ a ≫ ρ = 𝟙 V ∧ t' ≫ t ≫ π = π ≫ ρ ≫ a

/-- **A retract of an isomorphism along an isomorphism is an isomorphism**: given a retract
structure on the square `x ≫ a = δ ≫ t ≫ π` (`CategoryTheory.IsSquareRetract`) with `δ` and `π`
invertible, `x` is invertible. -/
lemma IsSquareRetract.isIso {U V V' S T : C} {x : U ⟶ V} {a : V ⟶ V'} {δ : U ⟶ S} [IsIso δ]
    {t : S ⟶ T} {π : T ⟶ V'} [IsIso π] {hsq : x ≫ a = δ ≫ t ≫ π} (h : IsSquareRetract hsq) :
    IsIso x := by
  obtain ⟨t', ρ, ht, ha, hc⟩ := h
  refine isIso_of_comp_eq_of_retraction (w := δ ≫ t) (w' := t' ≫ inv δ) ha ?_
    (by rw [hsq, Category.assoc]) ?_
  · rw [Category.assoc, reassoc_of% ht, IsIso.hom_inv_id]
  · rw [Category.assoc, Category.assoc, IsIso.inv_hom_id_assoc, hc]

section Monoidal

open MonoidalCategory

variable [MonoidalCategory C]

/-- A *tensor retract structure* on a commutative square `x ≫ a = δ ≫ (u₁ ⊗ u₂) ≫ π`
```
  U --δ--> S₁ ⊗ S₂ --u₁ ⊗ u₂--> T₁ ⊗ T₂
  |                                |
  x                                π
  v                                v
  V --------------a--------------> V'
```
consists of retractions `r₁` of `u₁` and `ρ` of `a` such that `π` carries the idempotent
`(r₁ ≫ u₁) ▷ T₂` to the idempotent `ρ ≫ a`. -/
def IsTensorRetract {U V V' S₁ S₂ T₁ T₂ : C} {x : U ⟶ V} {a : V ⟶ V'} {δ : U ⟶ S₁ ⊗ S₂}
    {u₁ : S₁ ⟶ T₁} {u₂ : S₂ ⟶ T₂} {π : T₁ ⊗ T₂ ⟶ V'} (_ : x ≫ a = δ ≫ (u₁ ⊗ₘ u₂) ≫ π) : Prop :=
  ∃ (r₁ : T₁ ⟶ S₁) (ρ : V' ⟶ V), u₁ ≫ r₁ = 𝟙 S₁ ∧ a ≫ ρ = 𝟙 V ∧
    ((r₁ ≫ u₁) ▷ T₂) ≫ π = π ≫ ρ ≫ a

/-- A tensor retract structure (`CategoryTheory.IsTensorRetract`) with `u₂` invertible gives a
retract structure (`CategoryTheory.IsSquareRetract`), with the retraction `r₁ ⊗ u₂⁻¹` of
`u₁ ⊗ u₂`. -/
lemma IsTensorRetract.isSquareRetract {U V V' S₁ S₂ T₁ T₂ : C} {x : U ⟶ V} {a : V ⟶ V'}
    {δ : U ⟶ S₁ ⊗ S₂} {u₁ : S₁ ⟶ T₁} {u₂ : S₂ ⟶ T₂} [IsIso u₂] {π : T₁ ⊗ T₂ ⟶ V'}
    {hsq : x ≫ a = δ ≫ (u₁ ⊗ₘ u₂) ≫ π} (h : IsTensorRetract hsq) : IsSquareRetract hsq := by
  obtain ⟨r₁, ρ, hr₁, ha, hc⟩ := h
  refine ⟨r₁ ⊗ₘ inv u₂, ρ, ?_, ha, ?_⟩
  · rw [tensorHom_comp_tensorHom, hr₁, IsIso.hom_inv_id, tensorHom_id, id_whiskerRight]
  · rw [← Category.assoc, tensorHom_comp_tensorHom, IsIso.inv_hom_id, tensorHom_id, hc]

end Monoidal

end CategoryTheory
