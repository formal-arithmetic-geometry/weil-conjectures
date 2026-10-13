/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.RingTheory.SelfTorConormalComparisonPredicate

/-! Uniqueness of the normalized self-Tor comparison. -/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry

/-- The Koszul normalization determines a comparison uniquely.
Source: Stacks Project, Tag 00LS (comparison of free complexes with resolutions),
with the normalization of Tag 09PQ used in the parent theorem.
(blueprint: new-r4-self-tor-conormal-comparison-unique).

Proof: Lift the n entries of any pure conormal wedge to ideal elements g,
using the surjection I -> I/I². Use the Koszul complex on that tuple and its
standard basis vectors. Its terms are free. The quotient augmentation kills
its first differential, so lift it inductively to any projective resolution
of A/I: lift degree zero against the surjective augmentation, degree one
against its kernel, and successive degrees against the exact differentials.
After tensoring with A/I all Koszul differentials vanish, since every g lies
in I. Thus the standard top wedge tensored with one has a cycle preimage z.
The two normalization hypotheses identify c and d on the conormal wedge
with the same homology class, after the same resolution isomorphism; cancel
that isomorphism. Pure wedges span over A/I. Since A -> A/I is surjective,
A-linearity also propagates equality to every A/I-multiple of a pure wedge,
and then to their sums. This proves equality of the morphisms. For n=0
use the empty tuple: the empty wedge is the unit and generates A/I. For
I=A the source is zero; for I=0 its positive exterior degrees are zero.
No regularity hypothesis is used. -/
theorem selfTorConormalComparison_unique (A : Type u) [CommRing A]
    (I : Ideal A) (n : ℕ)
    (c d : conormalExteriorModule A I n ⟶
      ((Tor' (ModuleCat.{u} A) n).obj (ModuleCat.of A (A ⧸ I))).obj
        (ModuleCat.of A (A ⧸ I)))
    (hc : IsSelfTorConormalComparison A I n c)
    (hd : IsSelfTorConormalComparison A I n d) : c = d := by sorry

end AlgebraicGeometry
