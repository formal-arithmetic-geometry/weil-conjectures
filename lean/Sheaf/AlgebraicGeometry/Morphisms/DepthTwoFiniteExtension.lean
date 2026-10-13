/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Sheaf.RingTheory.Depth

/-!
# Finite extension with depth two along the boundary

Source: Stacks Project, Tag 0EY6, assertions (1) and (2).
(blueprint: lem-sbc-depth-two-finite-extension)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- A finite etale cover extends to a finite scheme with depth two along the boundary.

Source: Stacks Project, Tag 0EY6, assertions (1) and (2).
(blueprint: lem-sbc-depth-two-finite-extension)

Proof: Write j for the inclusion of U. Work on an affine Noetherian open V of L;
U intersect V is quasi-compact. Extend the finite locally free module f_* O_X from
U intersect V to a finite coherent module M on V. Replace M by its double dual N,
which still restricts to f_* O_X. At a missing point the local ring has a regular
sequence of length two. A finite presentation of M's dual realizes N as the kernel
of a map between finite free modules. The first regular element is injective on N.
To check the second modulo the first, do the calculation in the free source; if
n = x m and n is in the kernel, then x d(m) = 0 in the free target, so d(m) = 0.
Thus this regular pair remains regular on N, giving depth at least two there.
The depth-two Hartogs restriction isomorphism (Stacks, Tag 0E9I) identifies N with
j_* f_* O_X. Consequently B = j_* f_* O_X is coherent, locally on L, and carries
its canonical algebra structure. Set E to be the relative spectrum of B. Coherence
makes p finite; restriction of the algebra gives the isomorphism over U. The
finite-algebra depth comparison (Tag 0AUK) transfers the depth of B at missing
points to the stalks of E above them. No global quasi-compactness is needed.
For U = L use X, and the empty cover gives the zero algebra and empty scheme.
This is the construction in 0EY6, with the double-dual argument spelling out the
coherence/depth step without an integrality assumption. -/
theorem exists_finite_extension_of_depth_two
    {L : Scheme.{u}} [IsLocallyNoetherian L] (U : L.Opens)
    (hboundary : ∀ y : L, y ∉ U →
      (2 : ℕ∞) ≤ IsLocalRing.depth (R := L.presheaf.stalk y) (L.presheaf.stalk y))
    {X : Scheme.{u}} (f : X ⟶ U.toScheme) [IsFinite f] [Etale f] :
    ∃ (E : Scheme.{u}) (p : E ⟶ L), IsFinite p ∧
      (∀ z : E, p z ∉ U →
        (2 : ℕ∞) ≤ IsLocalRing.depth (R := E.presheaf.stalk z) (E.presheaf.stalk z)) ∧
      ∃ e : (p ⁻¹ᵁ U).toScheme ≅ X, e.hom ≫ f = p ∣_ U := by sorry

end AlgebraicGeometry.Scheme
