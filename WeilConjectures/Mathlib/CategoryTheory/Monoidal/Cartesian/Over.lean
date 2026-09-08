/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# Points of an object of `Over X` valued in the monoidal unit

The monoidal unit of the cartesian monoidal category `Over X` is `X` itself, seen as an object
over itself via the identity. Hence a morphism `𝟙_ (Over X) ⟶ Y` is the same thing as a section
of the structure morphism `Y.hom : Y.left ⟶ X`.

## Main results

- `CategoryTheory.Over.unitHomEquiv`: morphisms `𝟙_ (Over X) ⟶ Y` are sections of `Y.hom`.
-/

@[expose] public section

namespace CategoryTheory.Over

open Limits MonoidalCategory

variable {C : Type*} [Category* C] [HasPullbacks C]

attribute [local instance] cartesianMonoidalCategory

variable {X : C}

/-- A morphism from the monoidal unit of `Over X` to `Y` is the same thing as a section of the
structure morphism of `Y`. -/
@[simps apply_coe]
noncomputable def unitHomEquiv (Y : Over X) :
    (𝟙_ (Over X) ⟶ Y) ≃ {p : X ⟶ Y.left // p ≫ Y.hom = 𝟙 X} where
  toFun f := ⟨f.left, Over.w f⟩
  invFun p := Over.homMk p.1 p.2
  left_inv _ := Over.OverMorphism.ext rfl
  right_inv _ := rfl

end CategoryTheory.Over
