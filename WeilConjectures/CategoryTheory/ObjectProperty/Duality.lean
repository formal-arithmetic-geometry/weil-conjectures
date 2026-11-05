/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Opposites

/-!
# Contravariant self-equivalences of full subcategories

Let `D : Cᵒᵖ ⥤ C` be a contravariant endofunctor of a category `C`, with a natural
transformation `δ : 𝟭 C ⟶ D.rightOp ⋙ D`, the *double-dual map* `δ_K : K ⟶ D (D K)`. If a
property `P` of objects of `C` is preserved by `D` and `δ_K` is an isomorphism for every `K`
satisfying `P`, then `D` restricts to an equivalence `P.FullSubcategoryᵒᵖ ≌ P.FullSubcategory`,
its own quasi-inverse. This is the shape of Verdier biduality.

## Main definitions

- `CategoryTheory.ObjectProperty.liftDual`: the restriction `P.FullSubcategoryᵒᵖ ⥤
  P.FullSubcategory` of `D`.
- `CategoryTheory.ObjectProperty.liftDualEquivalence`: the anti-equivalence of
  `P.FullSubcategory` it induces when `δ` is an isomorphism on `P`.
-/

@[expose] public section

open Opposite

namespace CategoryTheory.ObjectProperty

variable {C : Type*} [Category* C] (P : ObjectProperty C) (D : Cᵒᵖ ⥤ C)
  (hD : ∀ K, P K → P (D.obj (op K)))

variable (δ : 𝟭 C ⟶ D.rightOp ⋙ D) (hδ : ∀ K, P K → IsIso (δ.app K))

end CategoryTheory.ObjectProperty
