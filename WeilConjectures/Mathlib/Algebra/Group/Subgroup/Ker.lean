/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# The splitting lemma for commutative groups

A homomorphism `s : G →* H` of a commutative group `G` with a right inverse `i : H →* G`
(i.e. `s ∘ i = id`) splits `G` as `H × ker s`.

## Main definitions

- `MonoidHom.prodKerEquivOfLeftInverse`: the isomorphism `G ≃* H × ker s`, `g ↦ (s g, g / i (s g))`.
-/

@[expose] public section

namespace MonoidHom

variable {G H : Type*} [CommGroup G] [Group H]

end MonoidHom
