/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.LocalRing.Defs

/-!
# The Artin–Schreier kernel in a local ring

Source: blueprint sec-curve-estimates/sk-prop-h2/lem-sc-as-sequence.md, proof, first sentence;
Stacks Project, Étale Cohomology, Section 59.63 (Tag 0A3J).
(blueprint: lem-sc-local-ring-artin-schreier-kernel)
-/

universe u

namespace IsLocalRing

/-- In a local commutative ring with `p = 0`, the roots of `X ^ p - X` are exactly the
unique images of elements of `ZMod p` under the canonical cast.
Source: blueprint lem-sc-as-sequence, proof, first sentence; Stacks Project, Tag 0A3J.
(blueprint: lem-sc-local-ring-artin-schreier-kernel)

Proof:
1. Reduce a root `a` modulo the unique maximal ideal to the residue field. By
   `lem-sc-field-artin-schreier-kernel`, its image is the image of a unique `c : ZMod p`.
2. Set `b = a - ZMod.cast c`. Then `b` belongs to the maximal ideal and `b ^ p = b`,
   by the characteristic-`p` binomial theorem and the field root calculation. Since
   `p ≥ 2`, also `b ^ (p - 1)` is in the maximal ideal. Hence `1 - b ^ (p - 1)` is a unit
   by `lem-weil-pbc-local-ring-unit-criterion` (Stacks Tag 00E9). The equality
   `b * (1 - b ^ (p - 1)) = 0` gives `b = 0`, so `a = ZMod.cast c`.
3. Conversely, every `c : ZMod p` satisfies `c ^ p = c` by the field root calculation;
   the canonical ring map preserves this equation. If two constants have equal images
   in the local ring, reduction to the residue field and injectivity of its prime-field
   map give equality of the constants. This proves the asserted unique correspondence,
   equivalently the bijection from `ZMod p` to the root set. -/
theorem pow_eq_self_iff_existsUnique_zmod {R : Type u} [CommRing R] [IsLocalRing R]
    (p : ℕ) (hp : p.Prime) (hchar : (p : R) = 0) (a : R) :
    a ^ p = a ↔ ∃! c : ZMod p, (ZMod.cast c : R) = a := by
  sorry

end IsLocalRing
