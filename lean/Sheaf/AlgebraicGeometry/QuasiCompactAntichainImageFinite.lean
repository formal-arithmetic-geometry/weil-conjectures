/-
Copyright (c) 2026 The Weil Conjectures Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Weil Conjectures Project
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Noetherian

import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

/-!
# Finite specialization-antichain images of quasi-compact schemes

Source: the agent-formulated consequence of Stacks Project Tags 01RL and 0BA8,
with the affine argument of Tags 00FL, 00FK and 00FR
(blueprint: lem-sfb-quasicompact-antichain-image-finite).
-/

public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

/-- A morphism from a quasi-compact scheme to a locally Noetherian scheme has finite
image if any specialization between image points is an equality.

Source: agent-formulated consequence of Stacks Project, Morphisms, Tag 01RL and
Properties, Tag 0BA8 (blueprint: lem-sfb-quasicompact-antichain-image-finite).

Proof:
1. Choose Noetherian affine target charts using pqf-def-locnoeth. The affine basis
   (lem-weil-pbc-affine-opens-basis) and compactness of X give finitely many affine
   source opens covering X, each mapping into such a chart. By
   lem-weil-pbc-affine-opens-induced-ring-map-spec-square, these restrictions are
   induced by ring maps phi : R -> B. It suffices to show each affine image is finite.
2. Put K = ker(phi). The induced map R/K -> B is injective. The prime correspondence
   along R -> R/K identifies primes minimal over K with minimal primes of R/K:
   the inverse operations are quotient and contraction, both preserving inclusion.
3. The primes minimal over K form a finite set M by
   lem-sc-finite-minimal-primes-over-ideal. Apply
   lem-weil-pbc-injective-minimal-prime-lift to R/K -> B: every member of M is the
   contraction of a prime of B, so M is contained in the affine image.
4. Every prime p in that image contains K and hence contains a prime m minimal over K
   by lem-weil-pbc-prime-contains-minimal-prime. In the Zariski topology of
   def-weil-affine-spectrum, p lies in the closure of {m}. This remains true in Y:
   intersect any closed subset of Y containing m with the target chart. Both points
   belong to the image, so the hypothesis forces m = p. Thus the affine image is M.
5. The full image is a finite union of these finite images. For empty X the cover
   and image are empty. If K = R on a patch, then B is the zero ring, its spectrum
   and image are empty, and the minimal-prime arguments quantify over empty sets.
-/
theorem finite_range_of_specialization_antichain
    {X Y : AlgebraicGeometry.Scheme.{u}} [CompactSpace X]
    [AlgebraicGeometry.IsLocallyNoetherian Y] (h : X ⟶ Y)
    (hanti : ∀ (y : Y), y ∈ Set.range h →
      ∀ (y' : Y), y' ∈ Set.range h → y' ∈ closure ({y} : Set Y) → y = y') :
    (Set.range h).Finite := by
  sorry

end AlgebraicGeometry.Scheme.Hom
