/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q82
-/
module

public import Sheaf.RingTheory.ExcellentRing
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.FiniteType

/-!
# Quotients of universally catenary rings

Source: Stacks Project, Algebra, Tag 00NK, lemma-quotient-catenary, second assertion
(blueprint: lem-per-universal-catenarity-quotient).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace IsUniversallyCatenary

/-- Every quotient of a Noetherian universally catenary ring is universally catenary.
Source: Stacks Project, Algebra, Tag 00NK, lemma-quotient-catenary, second assertion
(blueprint: lem-per-universal-catenarity-quotient).

Proof:
1. Put R = A/I. For an ideal J of R, its inverse image K in A is finitely generated
   by def-weil-pbc-noetherian-ring. Surjectivity of A -> R shows that the images of
   generators of K generate J: lift an element of J, express its lift in those
   generators, and apply the quotient map. Hence R is Noetherian (Tag 00FN).
2. If B is a finite type R-algebra, choose finitely many algebra generators using
   def-weil-pbc-finite-type-algebra. Restrict scalars along A -> R. Lift the finitely
   many coefficients in each polynomial expression from R to A. The same generators
   then generate B as an A-algebra, so B is finite type over A (Tag 0ECE).
3. Universal catenarity of A, in def-exc-excellent-ring, implies that B is catenary.
   Restricting scalars changes neither B nor its prime chains, so both the finite
   bound on chain lengths and equality of saturated-chain lengths are retained.
   Since B was arbitrary, combine this with Step 1 to obtain universal catenarity
   of R (Tag 00NL). No primality or properness of I is needed.
-/
theorem quotient (A : Type u) [CommRing A] (hA : IsUniversallyCatenary A) (I : Ideal A) :
    IsUniversallyCatenary (A ⧸ I) := sorry

end IsUniversallyCatenary
