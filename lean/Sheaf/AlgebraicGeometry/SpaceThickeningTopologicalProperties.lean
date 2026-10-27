/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q24
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Mathlib.Topology.Homeomorph.Defs

/-! # Topological morphism properties under arbitrary algebraic-space thickenings

Source: Stacks Project, More on Morphisms of Spaces, Tag 09ZY,
lemma-thicken-property-morphisms, parts (3), (4), (6)
(blueprint: lem-sfb-space-thickening-topological-properties).

Quasi-compactness is written as the compact-open preimage condition on the specified
point topology. Closed immersions use the existing representable scheme-test predicate.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Quasi-compactness, quasi-separatedness, separatedness and universal closedness are
invariant in a commuting square with arbitrary thickenings as its vertical arrows.
Source: Stacks Project, Tag 09ZY, lemma-thicken-property-morphisms, parts (3), (4), (6)
(blueprint: lem-sfb-space-thickening-topological-properties).

Proof:
1. The homeomorphisms induced by i and j identify the underlying maps of f and f'.
Transport compact open subsets along j, and their inverse images along i. Transporting
open covers and finite subcovers in both directions proves the quasi-compactness clause.
2. For any T' → Y', put T = Y ×_{Y'} T', W = X ×_Y T and W' = X' ×_{Y'} T'.
By lem-trf-space-fibre-products-etale-covers these are algebraic spaces. On test objects,
forgetting the middle entry identifies W with X ×_{Y'} T' and with X ×_{X'} W'.
By lem-sfb-space-thickening-base-change, W → W' and T → T' are homeomorphisms.
If f is universally closed, the projection W → T is closed. Conjugating this projection
by the two homeomorphisms shows W' → T' is closed, proving the forward implication.
3. Conversely, for T → Y let V = X' ×_{Y'} T. Monicity of j cancels j in the
fibre-product equation, so X ×_Y T = X ×_{X'} V. Its map to V is a base change
of i, hence a homeomorphism. If f' is universally closed, V → T is closed, and
composing with this homeomorphism proves universal closedness of f. The arguments so far
use only monicity and homeomorphisms after every base change of the vertical arrows.
4. Put D = X ×_Y X and D' = X' ×_{Y'} X'. Monicity of j identifies D with
X ×_{Y'} X. The comparison D → D' factors through X ×_{Y'} X'; both arrows
are base changes of i. They are monomorphisms and homeomorphisms after every base change
by lem-sfb-space-thickening-base-change. The composite has the same properties, since its
base changes factor into base changes of those two arrows. The square of diagonals with
vertical arrows i and D → D' commutes, as checked on the two projections.
5. Apply steps 1--3 to this diagonal square. Step 1 proves the quasi-separatedness
clause. Steps 2--3 give simultaneous universal closedness of the diagonals.
By lem-sfb-space-separated-diagonal-closed this is equivalent to their being closed
immersions, giving the separatedness clause. No finite-order, flatness, local finite-type
or cartesian-square hypothesis enters any step. -/
theorem thickening_topological_properties_iff {B : Scheme.{u}}
    {X X' Y Y' : AlgebraicSpace B} (i : X ⟶ X') (j : Y ⟶ Y')
    (f : X ⟶ Y) (f' : X' ⟶ Y')
    (hi : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom)
    (hj : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) j.hom.hom)
    (hi_top : IsHomeomorph (mapPoint i.hom.hom))
    (hj_top : IsHomeomorph (mapPoint j.hom.hom))
    (hcomm : i ≫ f' = f ≫ j) :
    ((∀ V : Set (Point Y.obj.obj), IsOpen V → IsCompact V →
        IsCompact (mapPoint f.hom.hom ⁻¹' V)) ↔
      (∀ V : Set (Point Y'.obj.obj), IsOpen V → IsCompact V →
        IsCompact (mapPoint f'.hom.hom ⁻¹' V))) ∧
    ((∀ V : Set (Point (Limits.pullback f.hom.hom f.hom.hom)), IsOpen V → IsCompact V →
        IsCompact (mapPoint (Limits.pullback.diagonal f.hom.hom) ⁻¹' V)) ↔
      (∀ V : Set (Point (Limits.pullback f'.hom.hom f'.hom.hom)), IsOpen V → IsCompact V →
        IsCompact (mapPoint (Limits.pullback.diagonal f'.hom.hom) ⁻¹' V))) ∧
    (MapIsSeparated f ↔ MapIsSeparated f') ∧
    (MapIsUniversallyClosed f ↔ MapIsUniversallyClosed f') := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
