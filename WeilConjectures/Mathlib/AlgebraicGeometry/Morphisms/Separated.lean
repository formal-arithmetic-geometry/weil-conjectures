/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# A section of a separated morphism is a closed immersion

## Main statements

- `AlgebraicGeometry.IsClosedImmersion.of_comp_eq_id`: if `s ≫ f = 𝟙` and `f` is separated, then
  `s` is a closed immersion.
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

/-- A section of a separated morphism is a closed immersion. -/
@[stacks 01KT]
lemma IsClosedImmersion.of_comp_eq_id {f : X ⟶ Y} {s : Y ⟶ X} (hs : s ≫ f = 𝟙 Y)
    [IsSeparated f] : IsClosedImmersion s := by
  have : IsClosedImmersion (s ≫ f) := hs ▸ inferInstance
  exact .of_comp s f

end AlgebraicGeometry
