/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Claude
-/
module

public import Mathlib.CategoryTheory.EssentialImage

/-!
# The essential image of the inclusion of a full subcategory

The essential image of the inclusion `P.ι` of the full subcategory defined by a property `P`
of objects is the closure of `P` under isomorphisms (`CategoryTheory.ObjectProperty.essImage_ι`).
In particular it is contained in `P` when `P` is closed under isomorphisms
(`CategoryTheory.ObjectProperty.essImage_ι_le`).
-/

@[expose] public section

namespace CategoryTheory.ObjectProperty

variable {C : Type*} [Category* C] (P : ObjectProperty C)

/-- The essential image of the inclusion `P.ι` is the closure of `P` under isomorphisms. -/
lemma essImage_ι : P.ι.essImage = P.isoClosure := by
  ext X
  constructor
  · rintro ⟨Y, ⟨e⟩⟩
    exact ⟨Y.1, Y.2, ⟨e.symm⟩⟩
  · rintro ⟨Y, hY, ⟨e⟩⟩
    exact ⟨⟨Y, hY⟩, ⟨e.symm⟩⟩

/-- If `P` is closed under isomorphisms, the essential image of `P.ι` is contained in `P`. -/
lemma essImage_ι_le [P.IsClosedUnderIsomorphisms] : P.ι.essImage ≤ P := by
  rw [essImage_ι, isoClosure_eq_self]

end CategoryTheory.ObjectProperty
