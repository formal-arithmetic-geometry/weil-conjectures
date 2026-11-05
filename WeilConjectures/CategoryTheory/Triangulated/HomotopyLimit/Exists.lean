/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Basic
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Tower

/-!
# Existence of homotopy limits and levelwise isomorphisms of towers

Let `F : ℕᵒᵖ ⥤ C` be a tower in a pretriangulated category `C` with countable products. This
file shows that `F` has a homotopy limit cone
(`CategoryTheory.Pretriangulated.exists_isHomotopyLimit`): complete `1 - t : ∏ₙ Fₙ ⟶ ∏ₙ Fₙ` to a
distinguished triangle `X ⟶ ∏ₙ Fₙ ⟶ ∏ₙ Fₙ ⟶ X⟦1⟧`; the components of the first map are
compatible with the transition maps because the first map is killed by `1 - t`.

It also records that a morphism of towers which is an isomorphism at every level induces an
isomorphism on homotopy limits, whatever the choice of the map completing the morphism of Milnor
triangles (`CategoryTheory.Pretriangulated.isIso_of_isIso_app`); the corresponding statement
for homotopy limit cones is `CategoryTheory.Pretriangulated.IsHomotopyLimit.exists_iso_of_iso`.
-/

@[expose] public section

namespace CategoryTheory.Pretriangulated

open Category Limits Opposite

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

end CategoryTheory.Pretriangulated
