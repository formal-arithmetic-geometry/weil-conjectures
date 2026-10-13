/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C4
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Sheaf.RingTheory.Depth
import Sheaf.AlgebraicGeometry.AffineMorphismRelativeSpec

/-!
# Uniqueness of finite extensions with depth two at the boundary

Source: Stacks Project, Tag 0EY6, proof of assertion (2).
(blueprint: lem-sbc-depth-two-finite-extension-uniqueness)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- An isomorphism on an open extends between finite schemes of depth at least
two above its complement. No etaleness or depth assumption on the base is needed.

Source: Stacks Project, Tag 0EY6, converse in the proof of (2); Tags 0AUK and 0E9I.
(blueprint: lem-sbc-depth-two-finite-extension-uniqueness)

Proof: Write j for the open immersion U -> L. Finiteness makes the two direct
image algebras coherent. At a point y of L minus U, their depths as modules
over O_L,y are the minima of the depths of the source stalks over y (0AUK).
Both are therefore at least two; a zero algebra stalk has infinite depth.
Hartogs (0E9I) says that each direct image algebra maps isomorphically to
j_* of its restriction to U. These maps are the canonical restriction maps,
so they are maps of algebras as well as module isomorphisms. The supplied
isomorphism e over U identifies the restricted algebras. Push it forward and
compose with the two canonical Hartogs isomorphisms to identify the original
algebras. The contravariant equivalence between affine L-schemes and
quasi-coherent O_L-algebras gives an isomorphism F -> E over L. The equation
that it is over L is precisely i.hom followed by p equals r. This argument
uses only finiteness and the two source boundary depth bounds, not the base
depth or etaleness hypotheses used in 0EY6 to construct an extension.
For U = L it is the given isomorphism (inverted); for empty sources the same
canonical restriction and relative-spectrum argument applies. -/
theorem iso_of_finite_depth_two_extensions
    {L : Scheme.{u}} [IsLocallyNoetherian L] (U : L.Opens)
    {F E : Scheme.{u}} (r : F ⟶ L) (p : E ⟶ L) [IsFinite r] [IsFinite p]
    (hF : ∀ z : F, r z ∉ U →
      (2 : ℕ∞) ≤ IsLocalRing.depth (R := F.presheaf.stalk z) (F.presheaf.stalk z))
    (hE : ∀ z : E, p z ∉ U →
      (2 : ℕ∞) ≤ IsLocalRing.depth (R := E.presheaf.stalk z) (E.presheaf.stalk z))
    (e : (p ⁻¹ᵁ U).toScheme ≅ (r ⁻¹ᵁ U).toScheme)
    (he : e.hom ≫ r ∣_ U = p ∣_ U) :
    ∃ i : F ≅ E, i.hom ≫ p = r := by sorry

end AlgebraicGeometry.Scheme
