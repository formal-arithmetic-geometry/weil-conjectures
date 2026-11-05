/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Yoneda

/-!
# Invertibility of mates along adjunctions with invertible unit

Let `L₁ ⊣ R₁` and `L₂ ⊣ R₂` be adjunctions and `α : G ⋙ L₂ ⟶ L₁ ⋙ H` an isomorphism
filling the square
```
  C₁ --L₁--> D₁
  |          |
  G          H
  v          v
  C₂ --L₂--> D₂
```
At `d`, the mate `R₁ ⋙ G ⟶ H ⋙ R₂` of `α` is the unit of `L₂ ⊣ R₂` at `G (R₁ d)`, followed by
`R₂` of `α`, followed by `R₂ H` of the counit `ε_d` of `L₁ ⊣ R₁`. Hence, if the unit of `L₂ ⊣ R₂` is
invertible, the mate is invertible at `d` as soon as `R₂ (H ε_d)` is
(`CategoryTheory.isIso_mateEquiv_app_of_isIso_map_counit`).

A morphism `φ : X ⟶ Y` is inverted by the right adjoint `R` of an adjunction `L ⊣ R` as soon as
composition with `φ` is bijective on morphisms out of the objects `L B`
(`CategoryTheory.Adjunction.isIso_map_of_bijective_comp`), by the Yoneda lemma.

-/

@[expose] public section

namespace CategoryTheory

open Category

section Mate

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  {G : A ⥤ C} {H : B ⥤ D} {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

end Mate

namespace Adjunction

variable {C D : Type*} [Category* C] [Category* D] {L : C ⥤ D} {R : D ⥤ C}

end Adjunction

end CategoryTheory
