/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Local regular generators for a smooth diagonal

Source: Stacks Project, Tags 067U and 067R, applied to the diagonal as a section of the
smooth first projection (blueprint: lem-sc-smooth-diagonal-regular-immersion).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The diagonal of a smooth morphism of pure relative dimension `d`, when it is closed,
has on an affine neighbourhood of every point either the unit ideal or an ideal generated
by a regular sequence of length `d`. The ideal is the kernel of the map on sections.
Source: Stacks Project, Tags 067U and 067R
(blueprint: lem-sc-smooth-diagonal-regular-immersion).

Proof: outside the closed diagonal image choose an affine neighbourhood in its complement;
the inverse image is empty, so the kernel is the unit ideal. At an image point, if `d = 0`,
the morphism is etale (def-sbc-smooth-morphisms), hence unramified (def-weil-etale-morphism),
and its diagonal is open (def-weil-unramified-morphism). Choose the affine neighbourhood
inside the open and closed image. The diagonal there is an isomorphism, its ideal is zero,
and the empty sequence is regular. If `d > 0`, choose standard smooth affine charts around
the source point (lem-sc-standard-smooth-local-relative-dimension). Their fibre product is
an open neighbourhood of the diagonal point, and the diagonal restricts to the affine
diagonal on that product. The standard smooth affine calculation supplies regular generators
of length `d` on an affine neighbourhood (lem-sc-standard-smooth-affine-diagonal-generators).
This neighbourhood and its ideal also give the required neighbourhood in the original
fibre product. -/
theorem exists_isRegular_smooth_diagonal_generators {X S : Scheme.{u}} (d : ℕ)
    (f : X ⟶ S) [SmoothOfRelativeDimension d f] [IsClosedImmersion (pullback.diagonal f)] :
    ∀ w : (pullback f f : Scheme.{u}), ∃ U : (pullback f f).affineOpens, w ∈ U.1 ∧
      (RingHom.ker ((pullback.diagonal f).app U.1).hom = ⊤ ∨
        ∃ r : List Γ(pullback f f, U.1), r.length = d ∧
          RingTheory.Sequence.IsRegular Γ(pullback f f, U.1) r ∧
          Ideal.ofList r = RingHom.ker ((pullback.diagonal f).app U.1).hom) := by
  sorry

end AlgebraicGeometry
