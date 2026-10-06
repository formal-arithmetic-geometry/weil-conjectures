/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Subobject.Basic

/-!
# The image of a subobject under a monomorphism

For a monomorphism `f : A ⟶ B` and a subobject `X` of `A`, the underlying object of
`(Subobject.map f).obj X` is isomorphic to the underlying object of `X`.

## Main definitions

- `CategoryTheory.Subobject.mapObjIso`
-/

@[expose] public section

namespace CategoryTheory.Subobject

variable {C : Type*} [Category* C]

/-- The underlying object of the image of a subobject `X` under `Subobject.map f` is isomorphic
to the underlying object of `X`. -/
noncomputable def mapObjIso {A B : C} (f : A ⟶ B) [Mono f] (X : Subobject A) :
    ((map f).obj X : C) ≅ (X : C) :=
  isoOfEqMk _ (X.arrow ≫ f) (by
    conv_lhs => rw [← mk_arrow X]
    rfl)

@[reassoc (attr := simp)]
lemma mapObjIso_hom_arrow {A B : C} (f : A ⟶ B) [Mono f] (X : Subobject A) :
    (mapObjIso f X).hom ≫ X.arrow ≫ f = ((map f).obj X).arrow := by
  simp [mapObjIso]

end CategoryTheory.Subobject
