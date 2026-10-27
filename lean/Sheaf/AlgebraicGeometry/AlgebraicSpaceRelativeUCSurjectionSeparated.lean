/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q41
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus

/-! # Relative separatedness descends along universally closed surjections

Source: Stacks Project, Morphisms of Spaces, Tag 05Z2(4)
(blueprint: lem-sfb-space-relative-uc-surjection-separated).

The base of the two structural morphisms is an arbitrary algebraic space over `S`.
Separatedness and universal closedness use the existing scheme-test diagonal and
point-topology definitions, respectively.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- Relative separatedness descends along a surjective universally closed morphism.
Source: Stacks Project, Morphisms of Spaces, Tag 05Z2(4)
(blueprint: lem-sfb-space-relative-uc-surjection-separated).

Proof:
1. Put A = U ×_B U, C = V ×_B V and F = a ×_B a. Factor F through U ×_B V;
   both factors are base changes of a. Universal closedness is stable under base
   change and composition, so F is universally closed. Comparing the projections
   gives F Δ_p = Δ_q a (lem-trf-space-fibre-products-etale-covers and
   def-sfb-space-morphism-properties).
2. By lem-sfb-space-separated-diagonal-closed, separatedness of p implies universal
   closedness of Δ_p. Hence h = F Δ_p is universally closed. This diagonal criterion
   works over an arbitrary algebraic-space target B and needs no separation of B/S.
3. For any algebraic space T → C, set R = T ×_C U and Q = T ×_C V. The preceding
   equality identifies R with Q ×_V U: on sections send (t,u) to ((t,a(u)),u),
   with inverse forgetting the repeated a(u). The map b : R → Q is surjective
   on points and continuous by lem-a1-space-point-open-calculus. If E is closed
   in |Q|, then b⁻¹(E) is closed and its image under the closed map |R| → |T|
   is closed. Surjectivity identifies this image with the image of E under |Q| → |T|.
   Thus every base change of Δ_q is closed on points.
4. Apply lem-sfb-space-separated-diagonal-closed to q: universal closedness of its
   diagonal implies that the diagonal is representable by closed immersions.
   Therefore q is separated. -/
theorem mapIsSeparated_of_surjective_universallyClosed
    {S : Scheme.{u}} (B U V : AlgebraicSpace S)
    (p : U ⟶ B) (q : V ⟶ B) (a : U ⟶ V) (hcomm : a ≫ q = p)
    (hsurj : Function.Surjective (mapPoint a.hom.hom))
    (hclosed : MapIsUniversallyClosed a) (hsep : MapIsSeparated p) :
    MapIsSeparated q := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
