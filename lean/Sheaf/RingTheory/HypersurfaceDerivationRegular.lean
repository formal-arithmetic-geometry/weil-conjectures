/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Regular hypersurfaces with a unit derivative

Source: Stacks Project, More on Algebra, Lemma Tag 07PF
(blueprint: lem-weil-pbc-hypersurface-derivation-regular).
-/

@[expose] public section

universe u

namespace IsRegularRing

/-- Stacks Project, More on Algebra, Lemma Tag 07PF:
(blueprint: lem-weil-pbc-hypersurface-derivation-regular).
The quotient of a regular ring by `f` is regular if an absolute derivation sends `f`
to a unit in the quotient. Absolute derivations are represented by `ℤ`-derivations:
additive maps are automatically `ℤ`-linear, and the Leibniz rule forces `D 1 = 0`.

Proof:
1. If `f` is a unit, the quotient is zero and has no primes. Otherwise, for each prime
   of the quotient, take its inverse image `p` in `R`. By
   `lem-weil-pbc-localization-at-prime-of-quotient`, its localization is `R_p / f R_p`.
2. Extend `D` to `R_p` using `lem-weil-pbc-derivation-extends`. An inverse relation
   for `D(f)` modulo `f` localizes, so the derivative remains a unit modulo `f`.
   If `f` is outside `p`, the quotient is zero. Otherwise, if `f` were in the square
   of the maximal ideal of `R_p`, Leibniz would put its derivative in that maximal ideal,
   contradicting the unit hypothesis. Thus `f` is outside the square, and
   `lem-weil-pbc-regular-local-hypersurface-criterion` gives a regular local quotient.
3. The quotient is Noetherian because `R` is Noetherian. All its prime localizations
   are regular local, so `lem-weil-pbc-regular-ring-local-criterion` gives regularity.
-/
theorem quotient_span_singleton_of_isUnit_derivation
    (R : Type u) [CommRing R] [IsRegularRing R] (f : R) (D : Derivation ℤ R R)
    (hunit : IsUnit (Ideal.Quotient.mk (Ideal.span ({f} : Set R)) (D f))) :
    IsRegularRing (R ⧸ Ideal.span ({f} : Set R)) := by
  sorry

end IsRegularRing
