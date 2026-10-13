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

Proof: The depth condition on E identifies p with the canonical finite extension
of its etale restriction by uniqueness in 0EY6(2). This identifies its flat base
changes with canonical extensions too. Enlarge U to the open where p is etale.
Any remaining bad point lies over the closed point, and the complement is nowhere
dense in that fibre. Choose a closed point of this complement in an affine fibre
chart. Realize its finite residue-field extension by a finite flat local base
change (Tag 07NE), and use an etale slice (Tag 057G) to get a section through it.
Complete a smooth affine chart in the section ideal. Its ring becomes
A[[x_1,...,x_d]] by Tag 05D5, with a flat completion map. Density excludes d = 0
and puts the generic point of the closed fibre in the etale open. Power-series
purity (0EYA) extends the etale restriction on this completed chart. Uniqueness of
the depth-two finite extension identifies this etale model with the pullback of p.
Faithfully flat descent at the chosen point contradicts its being bad. Thus p is
etale. The argument is local and includes empty E and U = L. In particular this
statement asserts etaleness of an already supplied finite morphism, and constructs
no extension. -/
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
    Etale p := by sorry

end AlgebraicGeometry.Scheme
