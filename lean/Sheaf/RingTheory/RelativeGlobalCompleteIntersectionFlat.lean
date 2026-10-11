/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.Paper.RelativeGlobalCompleteIntersectionPresentation
public import Mathlib.RingTheory.RingHom.Flat

/-!
# Flatness of relative global complete intersections

Source: Stacks Project, Algebra, Lemma Tag 00SW
(blueprint: lem-weil-pbc-relative-global-complete-intersection-flat).
-/

@[expose] public section

universe u

namespace Algebra

/-- A polynomial quotient that is a relative global complete intersection is flat over
its coefficient ring. Source: Stacks Project, Algebra, Lemma Tag 00SW.
(blueprint: lem-weil-pbc-relative-global-complete-intersection-flat)

Proof:
1. For a prime `q` of the quotient, let `q'` be its inverse image in the polynomial ring.
   Part (2) of `lem-weil-pbc-relative-global-complete-intersection-partial-local-flat`,
   with `i = c` in a complete-intersection presentation, makes the localized polynomial
   quotient flat over `R`. The isomorphism of
   `lem-weil-pbc-localization-at-prime-of-quotient` identifies it with the quotient
   localized at `q`. The hypothesis applies to the displayed equations themselves.
2. Let `p` be the inverse image of `q` in `R`. By
   `lem-weil-pbc-flat-over-localization`, the localized quotient is flat over `R_p`.
   Apply `lem-weil-pbc-flat-map-local-criterion` at every prime `q` to obtain flatness
   of the original ring map. If the quotient is zero, there are no primes and the
   same local criterion applies vacuously. -/
theorem flat_of_isRelativeGlobalCompleteIntersection_quotient
    (R : Type u) [CommRing R] (n c : ℕ) (relations : Fin c → MvPolynomial (Fin n) R)
    (h : IsRelativeGlobalCompleteIntersectionPresentation relations) :
    RingHom.Flat
      (algebraMap R (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range relations))) := by
  sorry

end Algebra
