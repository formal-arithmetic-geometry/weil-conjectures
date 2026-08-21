/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import Mathlib.CategoryTheory.Sites.Monoidal

/-!
# The monoidal category structure on sheaves is closed

If `A` is a closed symmetric monoidal category with suitable limits and `J` is a
Grothendieck topology with `HasWeakSheafify J A`, the category of presheaves `Cᵒᵖ ⥤ A`
is closed symmetric monoidal, sheafification `presheafToSheaf J A` is monoidal for the
localized monoidal structure `Sheaf.monoidalCategory`, and `sheafToPresheaf J A` is fully
faithful. Day's reflection theorem (`Monoidal.Reflective.monoidalClosed`) then shows that
the localized monoidal structure on `Sheaf J A` is closed.

## Main definitions

- `CategoryTheory.Sheaf.monoidalClosed`: the monoidal category structure on `Sheaf J A`
  obtained in `Sheaf.monoidalCategory` is closed.

Like `Sheaf.monoidalCategory` itself, this is not made a global instance.
-/

@[expose] public section

universe v₁ v₃ u₁ u₃

namespace CategoryTheory.Sheaf

open Enriched.FunctorCategory MonoidalClosed MonoidalClosed.FunctorCategory

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  (A : Type u₃) [Category.{v₃} A] [MonoidalCategory A] [SymmetricCategory A]
  [MonoidalClosed A] [HasWeakSheafify J A]
  [∀ (F₁ F₂ : Cᵒᵖ ⥤ A), HasFunctorEnrichedHom A F₁ F₂]
  [∀ (F₁ F₂ : Cᵒᵖ ⥤ A), HasEnrichedHom A F₁ F₂]

attribute [local instance] monoidalCategory

/-- The monoidal category structure on `Sheaf J A` obtained in `Sheaf.monoidalCategory`
is closed, by Day's reflection theorem applied to the reflective adjunction
`sheafificationAdjunction J A`. -/
@[implicit_reducible]
noncomputable def monoidalClosed : MonoidalClosed (Sheaf J A) :=
  Monoidal.Reflective.monoidalClosed (sheafificationAdjunction J A)

end CategoryTheory.Sheaf
