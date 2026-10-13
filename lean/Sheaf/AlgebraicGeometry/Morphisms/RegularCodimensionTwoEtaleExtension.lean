/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M2
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Extending finite etale covers across a regular codimension-two boundary

Source: Stacks Project, Tags 0BMA, 0EY7, 0EY6 and 0H2W.
(blueprint: lem-sbc-regular-codimension-two-etale-extension)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- A finite etale cover of an open extends across a regular boundary whose
local rings have dimension at least two.

Source: Stacks Project, Tag 0BMA (local purity), Tag 0EY7 (extension), and
Tag 0EY6(2) (uniqueness), and Tag 0H2W, final paragraph (the locally Noetherian form).
(blueprint: lem-sbc-regular-codimension-two-etale-extension)

Proof: Every missing point has a regular local ring of dimension at least two,
so local purity holds by Tag 0BMA. On a Noetherian affine open of L, Tag 0EY7
extends the supplied finite etale cover: take a generic point of a component
of the missing closed set, extend on its local punctured spectrum by local
purity, and spread the finite etale extension to a larger open. Noetherian
induction terminates this procedure. The given open contains all generic
and codimension-one points, since their stalks have dimension at most one.
On overlaps the finite etale algebras are finite locally free modules.
Regular local rings of dimension at least two have depth at least two;
the same holds for these locally free modules at the missing points.
The depth-two extension identity identifies each algebra with the direct
image of its restriction to V (the argument of Tag 0EY6(2)). Consequently
the given algebra isomorphism on V extends uniquely on each overlap.
Uniqueness gives the cocycle identity, and descent for finite etale
morphisms glues the extensions to p over L and their isomorphism over V.
This local gluing requires no global quasi-compactness or quasi-separatedness.
If the given cover is empty, use the empty cover of L. -/
theorem exists_finite_etale_extension_of_regular_codimension_two_boundary
    {L Y : Scheme.{u}} [IsLocallyNoetherian L]
    (V : L.Opens)
    (hboundary : ∀ z : L, z ∉ V → IsRegularLocalRing (L.presheaf.stalk z) ∧
      (2 : WithBot ℕ∞) ≤ ringKrullDim (L.presheaf.stalk z))
    (q : Y ⟶ V.toScheme) [IsFinite q] [Etale q] :
    ∃ (E : Scheme.{u}) (p : E ⟶ L), IsFinite p ∧ Etale p ∧
      ∃ e : Y ≅ (p ⁻¹ᵁ V).toScheme, e.hom ≫ (p ∣_ V) = q := by sorry

end AlgebraicGeometry.Scheme
