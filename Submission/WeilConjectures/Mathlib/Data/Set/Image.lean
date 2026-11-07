/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Data.Set.Image

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Complements on ranges and preimages

- `Set.range_eq_preimage_range_of_comm`: in a commutative square of maps whose left vertical
  map is surjective and whose right vertical map is injective, the range of the top map is
  the preimage of the range of the bottom map.
-/

@[expose] public section

namespace Set

variable {A B C D : Type*}

/-- In a commutative square

```
   A ────m───→ B
   │           │
   │ pA        │ pB
   ↓           ↓
   C ────g───→ D
```

with `pA` surjective and `pB` injective, the range of `m` is the preimage under `pB` of the
range of `g`. -/
lemma range_eq_preimage_range_of_comm {m : A → B} {pA : A → C} {pB : B → D} {g : C → D}
    (hpA : Function.Surjective pA) (hpB : Function.Injective pB) (hcomm : pB ∘ m = g ∘ pA) :
    range m = pB ⁻¹' range g := by
  rw [← preimage_image_eq (range m) hpB, ← range_comp, hcomm, range_comp, hpA.range_eq,
    image_univ]

end Set
