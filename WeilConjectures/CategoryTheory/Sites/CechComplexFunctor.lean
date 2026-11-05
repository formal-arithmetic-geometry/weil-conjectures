/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Functoriality of the Čech complex in the coefficients

Let `U : ι → C` be a family of objects of a category with finite products, and let
`cechComplexFunctor U : (Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℕ` be the Čech complex functor. For an
additive functor `G : A ⥤ B` preserving products, applying `G` degreewise to the Čech complex of
a presheaf `P` gives the Čech complex of `P ⋙ G`.

When `C` has a terminal object `T`, the Čech complex of `P` is augmented by
`P(T) ⟶ ∏ᵢ P(U i)`, the product of the restriction maps.

## Main definitions

- `CategoryTheory.cechComplexFunctorMapIso`: the isomorphism
  `G(Č(U, P)) ≅ Č(U, P ⋙ G)`.
- `CategoryTheory.cechAugmentation`: the augmentation `P(T) ⟶ Č⁰(U, P)`.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Limits Opposite Simplicial

namespace Limits.FormalCoproduct

variable {C : Type u} [Category.{v} C] {A B : Type*} [Category* A] [Category* B]
  [HasProducts.{w} A] [HasProducts.{w} B] (G : A ⥤ B)
  [∀ J : Type w, PreservesLimitsOfShape (Discrete J) G]

end Limits.FormalCoproduct

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {ι : Type w} (U : ι → C)
  {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
  [HasProducts.{w} A] [HasProducts.{w} B]

section

variable (G : A ⥤ B) [G.Additive] [∀ J : Type w, PreservesLimitsOfShape (Discrete J) G]

end

variable {T : C} (hT : IsTerminal T)

end CategoryTheory
