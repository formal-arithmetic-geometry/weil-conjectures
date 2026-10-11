/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
import Sheaf.AlgebraicGeometry.Thickening

/-!
# Universal first order thickenings of schemes

Source: Stacks Project, More on Morphisms, Section 37.7 (Tag 04F2), opening paragraph,
and Definition 37.7.2 (Tag 04F4) (blueprint: def-weil-pbc-universal-first-order-thickening).

## Main definitions

* `AlgebraicGeometry.IsUniversalFirstOrderThickening`: the universal lifting property.

## Main statements

* `AlgebraicGeometry.IsUniversalFirstOrderThickening.unique`: uniqueness up to unique
  isomorphism over the base.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A first order thickening `i : Z ⟶ Z'` over `X` is universal for `h : Z ⟶ X`
if every morphism from a first order thickening `T ⟶ T'` over `X` into `Z`
extends uniquely to a morphism `T' ⟶ Z'` over `X`. Neither source scheme is
required to be affine. Existence of such a thickening is not assumed.
Source: Stacks Project, Section 37.7 (Tag 04F2), opening paragraph
(blueprint: def-weil-pbc-universal-first-order-thickening). -/
def IsUniversalFirstOrderThickening {Z Z' X : Scheme.{u}}
    (h : Z ⟶ X) (i : Z ⟶ Z') (h' : Z' ⟶ X) : Prop :=
  IsFirstOrderThickening i ∧ i ≫ h' = h ∧
    ∀ {T T' : Scheme.{u}} (j : T ⟶ T') (b : T' ⟶ X) (a : T ⟶ Z),
      IsFirstOrderThickening j → j ≫ b = a ≫ h →
        ∃! a' : T' ⟶ Z', a' ≫ h' = b ∧ j ≫ a' = a ≫ i

/-- Two universal first order thickenings of `Z` over `X` admit exactly one
morphism over `X` extending the identity on `Z`; that morphism is an isomorphism.
Apply the lifting property of the second thickening to the first with `a = 𝟙 Z`.
Apply it symmetrically to obtain an inverse. Each composite and the identity
extend `𝟙 Z` over `X`, so uniqueness makes both composites identities.
Source: Stacks Project, Section 37.7 (Tag 04F2), opening paragraph and
Lemma 37.7.1 (Tag 04F3), first general remark
(blueprint: def-weil-pbc-universal-first-order-thickening). -/
theorem IsUniversalFirstOrderThickening.unique {Z Z₁ Z₂ X : Scheme.{u}}
    (h : Z ⟶ X) (i₁ : Z ⟶ Z₁) (h₁ : Z₁ ⟶ X)
    (i₂ : Z ⟶ Z₂) (h₂ : Z₂ ⟶ X)
    (H₁ : IsUniversalFirstOrderThickening h i₁ h₁)
    (H₂ : IsUniversalFirstOrderThickening h i₂ h₂) :
    (∃! φ : Z₁ ⟶ Z₂, φ ≫ h₂ = h₁ ∧ i₁ ≫ φ = i₂) ∧
      ∀ φ : Z₁ ⟶ Z₂, φ ≫ h₂ = h₁ → i₁ ≫ φ = i₂ → IsIso φ := by
  sorry

end AlgebraicGeometry
