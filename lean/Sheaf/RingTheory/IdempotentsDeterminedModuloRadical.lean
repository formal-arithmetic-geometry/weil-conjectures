/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Mathlib.Algebra.Group.Idempotent
import Mathlib.RingTheory.Jacobson.Ideal

/-!
# Idempotents determined modulo an ideal in the Jacobson radical

Source: Stacks Project, More on Algebra, Lemma 15.10.2 (Tag 09XF), with Definition
15.10.1 (Tag 0ELY) (blueprint: lem-weil-pbc-idempotents-determined-modulo-radical).
-/

universe u

namespace IsIdempotentElem

/-- Idempotents congruent modulo an ideal in the Jacobson radical are equal.
Source: Stacks Project, Tag 09XF, with Tag 0ELY
(blueprint: lem-weil-pbc-idempotents-determined-modulo-radical).

Proof: Localize at any maximal ideal `m`. Since `J` is contained in every maximal ideal,
the difference of the localized idempotents has zero residue. An idempotent `x` in a local
ring is zero or one: `x` and `1 - x` sum to one, so one is a unit, and their product is zero.
The two residue values are distinct, so the localized idempotents agree.

Put `d = e - e'`. Its localization is zero at every maximal ideal. If `d` were nonzero,
its annihilator would be a proper ideal, contained in some maximal ideal `m`. Vanishing
in that localization gives `s` outside `m` with `s * d = 0`. Then `s` belongs to the
annihilator and hence to `m`, a contradiction. Thus `d = 0` and `e = e'` (Stacks Tag 00HN).
-/
theorem eq_of_sub_mem_of_le_jacobson {R : Type u} [CommRing R]
    (J : Ideal R) (hJ : J ≤ Ideal.jacobson (⊥ : Ideal R))
    {e e' : R} (he : IsIdempotentElem e) (he' : IsIdempotentElem e')
    (hee' : e - e' ∈ J) : e = e' := by
  sorry

end IsIdempotentElem
