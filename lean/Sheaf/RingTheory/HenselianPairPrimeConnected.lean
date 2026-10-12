/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Connected.Basic
import Sheaf.RingTheory.IntegralOverHenselianPair

/-!
# Connected zero loci over a henselian pair

Source: Stacks Project, More on Algebra, Lemma 15.11.16 (Tag 09Y6)
(blueprint: lem-weil-pbc-henselian-pair-prime-connected).
-/

@[expose] public section

universe u

namespace PrimeSpectrum

/-- For a henselian pair `(A, I)` and a prime ideal `p`, the closed subset `V(p + I)`
is connected in its subspace topology, including nonemptiness.
Source: Stacks Project, More on Algebra, Lemma 15.11.16 (Tag 09Y6)
(blueprint: lem-weil-pbc-henselian-pair-prime-connected).

Proof:
1. The integral quotient map `A → A/p` preserves henselian pairs by
   `lem-weil-pbc-integral-over-henselian-pair`. The quotient is a nonzero domain, and
   `lem-weil-pbc-spec-quotient-closed-immersion` together with `def-weil-affine-spectrum`
   identifies the spectrum of its quotient by the image of `I` with `V(p + I)`.
2. For a nonzero domain with a henselian ideal, the quotient is nonzero: otherwise the
   idempotent in the zero quotient would have the two distinct lifts `0` and `1`, contrary
   to uniqueness in `def-weil-pbc-henselian-terminology` applied to the finite algebra `A`.
3. A disconnection of the quotient spectrum gives a nontrivial idempotent by
   `lem-weil-pbc-spec-clopen-idempotent`. Henselian lifting supplies an idempotent in the
   domain, necessarily `0` or `1`, a contradiction. Transport this connectedness, including
   nonemptiness as in `def-weil-connected-scheme`, through the homeomorphism in step 1. -/
theorem connectedSpace_zeroLocus_sup_of_henselian {A : Type u} [CommRing A]
    (I : Ideal A) [HenselianRing A I] (p : Ideal A) [p.IsPrime] :
    ConnectedSpace (zeroLocus ((p ⊔ I : Ideal A) : Set A)) :=
  sorry

end PrimeSpectrum
