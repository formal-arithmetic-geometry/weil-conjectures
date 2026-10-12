/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.Abelian.RightDerived.InjectivelyExactSquare

@[expose] public section

universe u v w
open CategoryTheory
namespace CategoryTheory.InjectivelyExactSquare
variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]

/-- Naturality of the transported boundary under a morphism of injectively exact squares.

Source: Mathlib `HomologicalComplex.HomologySequence.δ_naturality` and
`InjectiveResolution.rightDerived_app_eq`; apply these to the morphism of short exact
resolution sequences induced termwise by the four components of `φ`.
(blueprint: lem-sc-injectively-exact-square-boundary-square-naturality). -/
theorem boundary_square_naturality (S : InjectivelyExactSquare.{u, v, w} C) (n : ℕ) :
    ∀ (T : InjectivelyExactSquare.{u, v, w} C) (φ : S.toSquare ⟶ T.toSquare) (F : C),
      S.boundary F n ≫ (NatTrans.rightDerived φ.τ₁ (n + 1)).app F =
        (NatTrans.rightDerived φ.τ₄ n).app F ≫ T.boundary F n := by sorry

end CategoryTheory.InjectivelyExactSquare
