/-
Copyright (c) 2026 NH. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NH
-/
module

public import WeilConjectures.RingTheory.Depth
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import WeilConjectures.RingTheory.AssociatedPrimeMinimalOfDepth
import WeilConjectures.RingTheory.DepthQuotientNonzerodivisor
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Regular sequences in the image of a local homomorphism

Source: Stacks Project, Algebra, Tag 06LC (lemma-find-sequence-image-regular)
(blueprint: lem-sfb-local-map-image-regular-sequence).
-/

@[expose] public section

universe u v

set_option autoImplicit false

namespace IsLocalRing

/-- A local homomorphism into a Noetherian Cohen--Macaulay local ring whose extended
source maximal ideal has radical equal to the target maximal ideal admits a regular
sequence of length the target dimension in its image. The source need not be Noetherian.
Source: Stacks Project, Algebra, Tag 06LC (lemma-find-sequence-image-regular)
(blueprint: lem-sfb-local-map-image-regular-sequence).

Proof: Induct on the target dimension, keeping both rings and the map variable and
using the stronger depth bound `d ≤ depth B`. At dimension zero the empty sequence is
regular because `B` is nonzero (def-weil-pbc-regular-sequence).
For positive dimension, the associated primes of `B` are finite
(lem-weil-pbc-noetherian-associated-primes-finite), and nonempty by the description of
zerodivisors (lem-weil-pbc-noetherian-module-zerodivisors-union-associated-primes).
They are minimal (lem-weil-pbc-cm-local-associated-prime-minimal), hence strictly below
the maximal ideal since the dimension is positive. Their inverse images under the map
are prime ideals not containing the source maximal ideal: otherwise the extended ideal,
and hence its radical, would be contained in the corresponding target prime.
Prime avoidance (lem-weil-pbc-prime-avoidance) selects a source element in the maximal
ideal avoiding these inverse images. Its image `x` is a nonzerodivisor by the same
zerodivisor description, and lies in the target maximal ideal by locality.
The quotient `C = B/xB` is Noetherian local, of dimension `d - 1` and depth at least
`d - 1` (lem-weil-pbc-cm-local-quotient-nonzerodivisor-cm). The quotient is nonzero,
its maximal ideal is the image of the target maximal ideal, and the composite source
map is local (lem-weil-pbc-quotient-local-structure). The radical condition descends:
lift an element of the quotient maximal ideal to the target maximal ideal and take a
power lying in the original extended ideal. Conversely, the new extended ideal lies
in the quotient maximal ideal, which is prime and therefore radical.
Apply induction to the composite map into `C` and prepend the element already chosen.
The successive quotients for the tail identify with those in `C` by lifting coefficients
of the generated ideals; these identifications respect multiplication by the next
image element. All the required multiplications are injective and the final quotient
is nonzero (def-weil-pbc-regular-sequence). When `d = 1` the tail is empty and the final
quotient is `C` itself. The equality of depth and dimension supplies the initial bound. -/
theorem exists_isRegular_map_of_radical_map_maximalIdeal
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing B]
    (φ : A →+* B) (hlocal : (maximalIdeal B).comap φ = maximalIdeal A)
    (d : ℕ) (hdim : ringKrullDim B = (d : WithBot ℕ∞))
    (hdepth : depth (R := B) B = (d : ℕ∞))
    (hradical : ((maximalIdeal A).map φ).radical = maximalIdeal B) :
    ∃ as : List A, as.length = d ∧ (∀ a ∈ as, a ∈ maximalIdeal A) ∧
      RingTheory.Sequence.IsRegular B (as.map φ) := by
  sorry

end IsLocalRing
