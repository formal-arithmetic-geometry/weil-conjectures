/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-!
# Complements on the underlying maps of morphisms of schemes

- `AlgebraicGeometry.Scheme.range_comp_subset_range`: the image of a composition is
  contained in the image of the second factor.
- `AlgebraicGeometry.Scheme.range_eq_preimage_range_of_comm`: in a commutative square whose
  left vertical map is surjective and whose right vertical map is injective, the image of the
  top map is the preimage of the image of the bottom map.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {A B C D : Scheme.{u}}

lemma range_comp_subset_range (a : A ⟶ B) (b : B ⟶ C) : Set.range (a ≫ b) ⊆ Set.range b := by
  simp [Set.range_comp]

/-- In a commutative square

```
   A ────m───→ B
   │           │
   │ pA        │ pB
   ↓           ↓
   C ────g───→ D
```

with `pA` surjective and `pB` injective on points, the image of `m` is the preimage under
`pB` of the image of `g`. -/
lemma range_eq_preimage_range_of_comm (m : A ⟶ B) (pA : A ⟶ C) (pB : B ⟶ D) (g : C ⟶ D)
    [Surjective pA] (hpB : Function.Injective pB) (hcomm : m ≫ pB = pA ≫ g) :
    Set.range m = pB ⁻¹' Set.range g := by
  have h : Set.range (m ≫ pB) = Set.range (pA ≫ g) := by rw [hcomm]
  rw [← Set.preimage_image_eq (Set.range m) hpB]
  congr 1
  simpa [Set.range_comp, pA.surjective.range_eq] using h

end AlgebraicGeometry.Scheme
