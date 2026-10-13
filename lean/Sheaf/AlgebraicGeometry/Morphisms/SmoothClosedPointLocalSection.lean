/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.RingHom.Flat

/-!
# A flat local base change carrying a prescribed smooth-fibre point

Source: Stacks Project, Tag 0EYB, residue extension and étale slice; Tags 07NE and 057G.
(blueprint: lem-sbc-smooth-closed-point-local-section)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- A closed point in a smooth closed fibre is reached by a flat local base change whose
closed fibre has only one point.

Source: Stacks Project, Tag 0EYB, the two base changes before completion; Tags 07NE and 057G.
(blueprint: lem-sbc-smooth-closed-point-local-section)

Proof: The smooth fibre is locally of finite type over the residue field. A closed point
therefore has finite residue extension. Tag 07NE realizes this extension by a finite flat
local algebra A' over A. In the base-changed fibre choose the rational lift of x. Apply
Tag 057G to obtain an étale slice through this lift, then localize its affine coordinate
ring at the slice point to obtain B. The composite A -> B is flat and local. Both the
finite local extension and the localized étale extension have zero-dimensional closed
fibre; hence the sole prime over the maximal ideal of A is the maximal ideal of B.
The map from the local slice to the original smooth scheme is s. The residue lift and
the localization send its closed point to the image of x. No open subset or depth
hypothesis is involved. -/
theorem exists_smooth_closed_point_local_section
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {L : Scheme.{u}} (q : L ⟶ Spec (.of A)) [Smooth q]
    (x : q.fiber (IsLocalRing.closedPoint A)) (hx : IsClosed ({x} : Set _)) :
    ∃ (B : Type u) (_ : CommRing B) (_ : IsLocalRing B) (_ : IsNoetherianRing B),
      ∃ (φ : A →+* B), IsLocalHom φ ∧ φ.Flat ∧
        (∀ z, (Spec.map (CommRingCat.ofHom φ)) z = IsLocalRing.closedPoint A →
          z = IsLocalRing.closedPoint B) ∧
        ∃ (s : Spec (.of B) ⟶ L), s ≫ q = Spec.map (CommRingCat.ofHom φ) ∧
          s (IsLocalRing.closedPoint B) = q.fiberι (IsLocalRing.closedPoint A) x := by sorry

end AlgebraicGeometry.Scheme
