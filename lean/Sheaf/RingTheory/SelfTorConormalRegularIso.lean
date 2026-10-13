/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.RingTheory.SelfTorConormalComparison
public import Sheaf.RingTheory.KoszulRegularSequence

/-! # The canonical self-Tor comparison for a regular quotient

Source: Stacks Project, Tags 062I, 0BQY and 09PQ.
(blueprint: new-r4-self-tor-conormal-regular-iso). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- The normalized comparison is invertible for a Koszul-regular quotient.

Source: Stacks Project, Tags 062I, 0BQY and 09PQ.
(blueprint: new-r4-self-tor-conormal-regular-iso).

Proof: Let f be the r Koszul-regular generators. Their Koszul complex is a finite
free resolution of A/I. Use this resolution to compute Tor. After tensoring with A/I,
every differential coefficient is zero, and nth homology is its nth term, the nth
exterior power of (A/I)^r. The conormal basis theorem identifies I/I² with (A/I)^r,
sending the class of f_j to its standard basis vector. The normalization of the
canonical comparison identifies its value on each increasing wedge of these classes
with precisely the corresponding Koszul homology basis vector. It is consequently an
isomorphism. Equivalently apply the nth exterior power to the conormal basis equivalence
and compose with the zero-differential homology and resolution Tor equivalences; equality
with the canonical map follows by exterior generation and its normalization. For n=0
this sends the empty wedge to 1; for n>r both modules are zero. The same equivalences
cover r=0, A/I=0, and the zero ring. -/
theorem selfTorConormalComparison_isIso (A : Type u) [CommRing A]
    (I : Ideal A) (n r : ℕ) (f : Fin r → A)
    (hf : Ideal.span (Set.range f) = I) (hreg : RingTheory.Sequence.IsKoszulRegular f) :
    IsIso (selfTorConormalComparison A I n) := by sorry

end AlgebraicGeometry
