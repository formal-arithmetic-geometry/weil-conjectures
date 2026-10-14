/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.ZariskisMainTheorem
public import Sheaf.RingTheory.QuasiFiniteAtPrime

/-!
# The pointwise hypothesis conversion for Zariski's main theorem

Source: Stacks Project, Algebra, Tags 00PK, 00PL and 00Q9
(blueprint: lem-weil-pbc-integral-closure-zariski-main-away, proof step 1).

The former declaration in this module duplicated the conclusion of
`Algebra.ZariskisMainProperty.of_finiteType`. This declaration supplies only the
strictly separate conversion from the fibre formulation used by the Sheaf plan.
-/

@[expose] public section

universe u v

namespace Algebra

/-- A quasi-finite fibre at a prime gives Mathlib's `QuasiFiniteAt` instance.
Source: Stacks Project, Algebra, Theorem Tag 00Q9, via the fibre-spectrum
homeomorphism and Mathlib's `QuasiFiniteAt.of_isOpen_singleton_fiber`.

Proof: let `p` be the contraction of `q`. The hypothesis says that the singleton
of the canonical fibre-ring prime is open. The homeomorphism from the topological
fibre to the fibre-ring spectrum takes the singleton of `q` to this singleton.
Transport openness back along the homeomorphism and apply Mathlib's finite-type
criterion for quasi-finiteness at an isolated point of the fibre.
(blueprint: lem-weil-pbc-integral-closure-zariski-main-away, proof step 1).
-/
theorem zariskisMainProperty_of_isQuasiFiniteAtPrime
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (q : PrimeSpectrum S)
    (hq : IsQuasiFiniteAtPrime R S q) : QuasiFiniteAt R q.asIdeal := by
  let p := q.comap (algebraMap R S)
  let e := PrimeSpectrum.preimageHomeomorphFiber R S p
  apply QuasiFiniteAt.of_isOpen_singleton_fiber q
  exact e.isOpen_image.mp (by
    simpa only [Set.image_singleton, IsQuasiFiniteAtPrime] using hq)

end Algebra
