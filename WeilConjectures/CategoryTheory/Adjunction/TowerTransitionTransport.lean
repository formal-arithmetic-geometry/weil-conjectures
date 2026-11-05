/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic

/-! # Transport of adjunction-induced transitions along base change

Given adjunctions `E₀ ⊣ R₀`, `E₁ ⊣ R₁` with `Q ⋙ R₁ ≅ R₀`, the transition
`R₁ E₁ ⟶ R₀ E₀` is induced by the adjoint of the unit. Base change isomorphisms between
two such configurations, compatible with the units and with the comparison isomorphisms,
intertwine the transitions.

(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory

namespace CategoryTheory.Adjunction

variable {A A' B₀ B₁ B₀' B₁' : Type*} [Category A] [Category A'] [Category B₀] [Category B₁]
  [Category B₀'] [Category B₁']
  {E₀ : A ⥤ B₀} {R₀ : B₀ ⥤ A} (adj₀ : E₀ ⊣ R₀)
  {E₁ : A ⥤ B₁} {R₁ : B₁ ⥤ A} (adj₁ : E₁ ⊣ R₁)
  {E₀' : A' ⥤ B₀'} {R₀' : B₀' ⥤ A'} (adj₀' : E₀' ⊣ R₀')
  {E₁' : A' ⥤ B₁'} {R₁' : B₁' ⥤ A'} (adj₁' : E₁' ⊣ R₁')
  {Q : B₀ ⥤ B₁} {Q' : B₀' ⥤ B₁'} (c : Q ⋙ R₁ ≅ R₀) (c' : Q' ⋙ R₁' ≅ R₀')

variable (Ψ : A' ⥤ A) (M₀ : B₀' ⥤ B₀) (M₁ : B₁' ⥤ B₁)
  (σ₀ : R₀' ⋙ Ψ ≅ M₀ ⋙ R₀) (σ₁ : R₁' ⋙ Ψ ≅ M₁ ⋙ R₁)
  (s : Q' ⋙ M₁ ≅ M₀ ⋙ Q)
  (β₀ : Ψ ⋙ E₀ ≅ E₀' ⋙ M₀) (β₁ : Ψ ⋙ E₁ ≅ E₁' ⋙ M₁)

end CategoryTheory.Adjunction
