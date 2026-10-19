/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Fiber
public import Sheaf.RingTheory.Depth

import Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFiniteFlat
import Sheaf.AlgebraicGeometry.Morphisms.FlatDepthTwoFiniteFormallyUnramified

/-!
# Etaleness of a depth-two finite extension over a smooth local base

Source: Stacks Project, proof of Tag 0EYB, with uniqueness in Tag 0EY6(2).
(blueprint: lem-sbc-smooth-local-depth-two-finite-purity)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- A supplied finite depth-two extension is etale when its etale open is fibrewise dense.

Source: Stacks Project, proof of Tag 0EYB, and Tag 0EY6(2),(a),(b).
(blueprint: lem-sbc-smooth-local-depth-two-finite-purity)

Proof: Smoothness over the Noetherian affine base makes L locally Noetherian.
The formal-completion flatness theorem gives Flat p from fibre density and
the supplied extension's boundary depth condition. The flat depth-two purity
criterion then gives FormallyUnramified p. Its proof uses 0BJH, since every
source point of local dimension one must lie over U. Finiteness over a locally
Noetherian scheme supplies local finite presentation. Mathlib's criterion
combines flatness, formal unramifiedness and local finite presentation to give
Etale p. This proves the original statement from two separate assertions:
flatness by the completion argument, and absence of ramification for a flat
extension. Neither assertion is the original etaleness statement. -/
theorem etale_of_smooth_local_depth_two_finite_extension
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {L : Scheme.{u}} (q : L ⟶ Spec (.of A)) [Smooth q]
    (U : L.Opens)
    (haway : ∀ y : L, q y ≠ IsLocalRing.closedPoint A → y ∈ U)
    (hclosed : Dense (↑((q.fiberι (IsLocalRing.closedPoint A)) ⁻¹ᵁ U) :
      Set (q.fiber (IsLocalRing.closedPoint A))))
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth (R := A) A)
    {E : Scheme.{u}} (p : E ⟶ L) [IsFinite p] [Etale (p ∣_ U)]
    (hboundary : ∀ z : E, p z ∉ U →
      (2 : ℕ∞) ≤ IsLocalRing.depth (R := E.presheaf.stalk z) (E.presheaf.stalk z)) :
    Etale p := by
  have : IsLocallyNoetherian L := LocallyOfFiniteType.isLocallyNoetherian q
  have : Flat p :=
    flat_of_smooth_local_depth_two_finite_extension A q U haway hclosed hdepth p hboundary
  have : FormallyUnramified p :=
    formallyUnramified_of_flat_depth_two_finite_extension U p hboundary
  exact Etale.of_formallyUnramified_of_flat p

end AlgebraicGeometry.Scheme
