/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q85
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Operations
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Trace-one invariant finiteness

Source: ILO, Travaux de Gabber, Exposé VI, proof 3.7(b), printed p.75, motivates the
finite tame strict-local invariant quotient. The general trace-one algebraic statement
and skew-group proof below are agent-supplied, not asserted to be stated in ILO.
(blueprint: lem-per-trace-one-noetherian-invariant-finiteness)
-/

@[expose] public section

universe u v

open scoped BigOperators

namespace FixedPoints

/-- A commutative Noetherian ring with a finite group action and an element of group
trace one is finite over its Noetherian invariant subring. No faithfulness, invertibility
of the group order, or finite-type base algebra is required.

Source: ILO, Exposé VI, proof 3.7(b), printed p.75, motivates the invariant quotient;
the following general trace-one algebraic argument is agent-supplied.
(blueprint: lem-per-trace-one-noetherian-invariant-finiteness)

Proof:
1. Form the skew group ring S = direct sum over g of R[g], with multiplication
   (r[g])(s[h]) = r g(s)[gh]. On basis terms associativity follows from the action law,
   and distributivity extends it to sums. Embed R by r maps to r[1]. As a right R-module,
   S is finite free on [g], since r[g] = [g]g⁻¹(r). Use commutativity to regard right
   R-modules as left R-modules (def-weil-finitely-generated-module).
2. Choose a with trace one and set e = sum of g(a)[g]. Reindexing gives [h]e = e,
   hence e² = e. The coefficient-sum map sends re to r, so r maps to re is injective.
   Also (sum of r_g[g])e = (sum of r_g)e, and consequently Se = Re.
3. The corner C = eSe is a ring with unit e. Each c in C is uniquely re. Since
   [h]c = c and [h]re = h(r)e, injectivity gives r in A = R^G. Conversely b in A
   commutes with e, so be = ebe lies in C. Thus C = Ae and b maps to be is a ring
   isomorphism A to C; r maps to re identifies the A-module R with the right C-module Se.
4. The two-sided ideal I = SeS is a right R-submodule of the finite right R-module S.
   By lem-trf-noetherian-submodule-finitely-presented it has finitely many right
   R-generators y_j. Expand each y_j into finitely many products n_jk s_jk with n_jk
   in Se, and collect all n_jk as n_1,...,n_t. Then I = sum of n_i S: the right side
   contains every y_j and hence their right R-span, and is contained in I.
5. Multiply by e to get Se = Ie = sum of n_i S e. As n_i = n_i e, write
   n_i s e = n_i(ese). By step 3, ese = be for b in A. Write n_i = r_i e and use
   injectivity from step 2 to deduce that the r_i generate R over A
   (def-weil-finitely-generated-module).
6. Define the A-linear retraction rho(r) = sum of g(ar), which is invariant by
   reindexing and is the identity on A by trace one. For an ideal J of A, the ideal
   JR is finitely generated because R is Noetherian (def-weil-pbc-noetherian-ring).
   Expand its finite generators using elements of J and collect finitely many
   j_i in J generating JR. Apply rho to b = sum of j_i r_i for b in J to obtain
   b = sum of j_i rho(r_i). Thus every ideal J is finite, so A is Noetherian.
-/
theorem isNoetherianRing_and_finite_of_trace_one
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (G : Type v) [Group G] [Fintype G] [MulSemiringAction G R]
    (htrace : ∃ a : R, ∑ g : G, g • a = 1) :
    IsNoetherianRing (FixedPoints.subring R G) ∧ Module.Finite (FixedPoints.subring R G) R := by
  sorry

end FixedPoints
