/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Uniqueness of a cartesian lift along a morphism

`CategoryTheory.IsPullback.eq_of_comp_eq`: if the square

```
        q
   Z ───────→ T
   │          │
 𝟙 │          │ π
   ↓          ↓
   Z ───j───→ X
```

is cartesian, then `q` is the *only* morphism `Z ⟶ T` lying over `j`. This is the abstract
content of the uniqueness of the lift of a morphism along a morphism that is an isomorphism
over its image.
-/

@[expose] public section

namespace CategoryTheory

variable {C : Type*} [Category C] {Z T X : C} {q : Z ⟶ T} {j : Z ⟶ X} {π : T ⟶ X}

/-- **Uniqueness of a cartesian lift**: if the square with sides `q`, `𝟙 Z`, `π` and `j` is
cartesian, then any morphism `q' : Z ⟶ T` with `q' ≫ π = j` equals `q`. -/
theorem IsPullback.eq_of_comp_eq (h : IsPullback (𝟙 Z) q j π) {q' : Z ⟶ T}
    (hq' : q' ≫ π = j) : q' = q := by
  have hfst := h.lift_fst (𝟙 Z) q' (by rw [Category.id_comp, hq'])
  have hsnd := h.lift_snd (𝟙 Z) q' (by rw [Category.id_comp, hq'])
  rw [Category.comp_id] at hfst
  rw [← hsnd, hfst, Category.id_comp]

end CategoryTheory
