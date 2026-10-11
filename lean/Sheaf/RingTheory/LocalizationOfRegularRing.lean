/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# A localization of a regular ring is regular

Source: Stacks Project, Algebra, proof of Lemma Tag 0381, Step 3
(blueprint: lem-weil-pbc-localization-of-regular-ring).
-/

@[expose] public section

universe u v

namespace RingTheory

/-- A localization of a regular ring is regular.

Source: Stacks Project, Algebra, proof of Lemma Tag 0381, Step 3
(blueprint: lem-weil-pbc-localization-of-regular-ring).

The proof first obtains Noetherianity from the localization theorem, then identifies each
localization at a prime of `R'` with the corresponding localization of `R` at its inverse-image
prime.  The inverse-image prime is disjoint from `M`. Regularity of `R` makes its localization at
that prime regular local. The isomorphism preserves Noetherianity, the unique maximal ideal,
Krull dimension and a generating set of that ideal, so the localization of `R'` is regular
local. Together with Noetherianity, this proves `IsRegularRing R'` at every prime.  It uses
`lem-weil-pbc-localization-noetherian`,
`lem-weil-pbc-localization-prime-residue-field-iso`, and
`def-weil-pbc-localization-at-prime`.
-/
theorem isRegularRing_of_localization
    (R : Type u) (R' : Type v) [CommRing R] [CommRing R'] [IsRegularRing R]
    (M : Submonoid R) (φ : R →+* R')
    (hunit : ∀ s : M, IsUnit (φ s.1))
    (hsurj : ∀ y : R', ∃ r : R, ∃ s : M, ∃ u : R',
      IsUnit u ∧ φ s.1 * u = 1 ∧ y = φ r * u)
    (hzero : ∀ r : R, φ r = 0 → ∃ s : M, s.1 * r = 0) :
    IsRegularRing R' := by
  sorry

end RingTheory
