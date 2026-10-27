/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q117
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Operations
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Maximal

/-!
# Surjectivity of the group trace under tame inertia

Source: Stacks Project, Tags 0BRH, 0BRI, and 0BRJ in `more-algebra.tex`,
for invariants, integrality, and residue actions. The trace argument is the
agent-supplied consequence recorded in the DAG, not a verbatim statement of those tags.
(blueprint: lem-per-tame-inertia-surjective-group-trace)
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace MulSemiringAction

/-- If every inertia order is invertible in its residue field, every invariant is a group
trace, and in particular there is an element of trace one. No Noetherian, finite-type,
faithful-action, or invertibility-of-the-whole-group-order hypothesis is used.

Here `p.inertia G` consists of elements satisfying `g • r - r ∈ p` for every `r`.
This is exactly the stabilizer acting trivially on the residue field: identity on `R / p`
extends to its fraction field `p.ResidueField`, and the quotient embeds in that field.
The group sum is automatically invariant and linear over `FixedPoints.subring R G`;
its surjectivity is expressed by preimages of every element of this subring.

Source: Stacks Project, Tags 0BRH (`lemma-base-change-invariants`), 0BRI (`lemma-one-orbit`),
and 0BRJ (`lemma-one-orbit-geometric`) in `more-algebra.tex`, with the following
agent-supplied trace argument.
(blueprint: lem-per-tame-inertia-surjective-group-trace)

Proof:
1. Reindexing the group sum proves invariance; additivity and fixed-scalar linearity
   make its image an ideal J of the fixed ring A. It suffices that no maximal ideal contains J.
2. The orbit polynomial product_g (X - g(r)) is monic with coefficients in A and vanishes
   at r. Thus R is integral over A, without any finite-generation assumption (Tag 0BRI).
3. Given a maximal ideal m of A, lem-weil-pbc-integral-injective-lying-over gives a prime
   p above it. By lem-weil-pbc-integral-prime-over-maximal-maximal, p is maximal.
   Its G-orbit is a finite family of maximal ideals.
4. The field R / p identifies with p.ResidueField: send r/s to its residue quotient, and
   send a residue r to r/1. This uses def-weil-pbc-localization-at-prime. If D stabilizes p
   and H is its image in the automorphisms of this field, the kernel is p.inertia G.
   Each fiber of D -> H is an inertia coset, hence has the inertia group's order.
5. By lem-per-monoid-characters-linear-independent the sum of the distinct automorphisms
   in H is nonzero: a zero sum would contradict independence with every coefficient 1.
   Since H contains the identity, choose b with u = sum_sigma sigma(b) nonzero.
6. Distinct maximal ideals in the orbit of p are comaximal. By
   lem-pc-crt-ideal-quotient-product choose r with residue b at p and zero at the other
   orbit ideals. Terms outside D vanish modulo p. The remaining sum is |p.inertia G| u,
   which is nonzero by tameness. Thus the trace of r is outside p and hence outside m.
7. No maximal ideal of A contains J. By lem-weil-pbc-proper-ideal-contained-in-maximal,
   J = A. Choose a with trace 1; fixed-scalar linearity gives trace(ca) = c for every c in A.
   Conversely, surjectivity supplies a preimage of 1. For the zero ring, trace(0) = 0 = 1,
   so no nontriviality hypothesis is needed. -/
theorem groupTrace_surjective_of_isUnit_inertia
    (R : Type u) [CommRing R] (G : Type v) [Group G] [Fintype G]
    [MulSemiringAction G R]
    (htame : ∀ (p : Ideal R) [p.IsPrime],
      IsUnit (Nat.card (p.inertia G) : p.ResidueField)) :
    (∀ b : FixedPoints.subring R G, ∃ a : R, ∑ g : G, g • a = (b : R)) ∧
      (∃ a : R, ∑ g : G, g • a = 1) := by
  sorry

end MulSemiringAction
