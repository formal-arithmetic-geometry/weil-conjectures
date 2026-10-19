/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.Dynamics.Newton

@[expose] public section

/-- A local ring with nil maximal ideal satisfies simple-root lifting.
Source: Mathlib.Dynamics.Newton, `Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero`;
Stacks Project, Algebra, Tag 06RS
(blueprint: lem-weil-pbc-henselian-of-nil-maximal-ideal).

Proof: For a polynomial f and an approximate root x, f(x) lies in the maximal ideal,
hence is nilpotent. Since f'(x) is a unit, finite Newton iteration gives a root a with
x - a nilpotent: each iteration squares the error, so a sufficiently high iteration
has zero error. The derivative remains a unit since the correction is nilpotent.
The nilpotent difference a - x belongs to every prime ideal, in particular the maximal
ideal. This gives the defining simple-root lifting condition for a henselian local ring.
No uniform nilpotence exponent for the maximal ideal is required. -/
theorem henselianLocalRing_of_maximalIdeal_le_nilradical
    (R : Type*) [CommRing R] [IsLocalRing R]
    (hnil : IsLocalRing.maximalIdeal R ≤ nilradical R) : HenselianLocalRing R := by
  constructor
  intro f _ x hx hderiv
  obtain ⟨a, ha, _⟩ := Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero
    (show IsNilpotent (Polynomial.aeval x f) by simpa using mem_nilradical.mp (hnil hx))
    (show IsUnit (Polynomial.aeval x f.derivative) by simpa using hderiv)
  refine ⟨a, ?_, ?_⟩
  · simpa [Polynomial.IsRoot] using ha.2
  · exact nilradical_le_prime (IsLocalRing.maximalIdeal R)
      (by simpa only [mem_nilradical, neg_sub] using ha.1.neg)
