/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.Topology.Irreducible
public import Sheaf.AlgebraicGeometry.GeometricComponentCountBaseChange

import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.AlgebraicGeometry.GeometricGenericCoverSpread

/-!
# Generic constancy of geometric connected-component counts

Source: Stacks Project, More on Morphisms, Tag 055H,
`lemma-nr-geom-connected-components-good`
(blueprint: lem-sfb-geometric-connected-count-generic-constancy).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A finite-type family has constant geometric connected-component count on a nonempty
relatively open subset of every nonempty irreducible closed subset of its base.
The subtype `Z` carries the relative topology. `IsIrreducible Z` includes nonemptiness.
Counts use `ConnectedComponents`, not irreducible components, and `ENat.card` records
infinite counts as infinity and the empty fibre as zero. Universally quantifying the
algebraically closed residue-field extension expresses the well-defined count of 055F.

Source: Stacks Project, More on Morphisms, Tag 055H,
`lemma-nr-geom-connected-components-good`
(blueprint: lem-sfb-geometric-connected-count-generic-constancy).

Proof:
1. By `lem-sc-scheme-sober`, the closed irreducible subset Z is the closure of its
   generic point. Give it the reduced induced closed structure using
   `lem-weil-pbc-reduced-induced-closed-subscheme` and base change the family to Z.
   Finite type is preserved by `lem-sfb-finite-type-composition-base-change`, and
   `lem-weil-pbc-geometric-component-count-base-change` identifies the counts.
2. Apply `lem-sfb-etale-generic-component-splitting`: an irreducible affine finite etale
   cover of a nonempty open makes all generic irreducible components geometrically
   irreducible. Work on this cover and retain finite type by base change.
3. The generic fibre is finite type over a field, hence Noetherian by
   `lem-weil-pbc-finite-type-over-noetherian`. Its irreducible components form a finite
   closed cover by `lem-weil-pbc-noetherian-finite-components` and
   `lem-sc-irreducible-components-cover`.
4. Form their intersection graph. The union of vertices in a graph component is
   connected, since no separation splits a vertex or an edge or a path. Different
   unions are disjoint and clopen, so they are exactly the connected components.
   Let n be their finite number. An empty generic fibre gives the empty graph and n = 0.
5. Apply `lem-sbc-geometric-generic-cover-spread` to this cover with the identity
   generic field extension. On an open neighbourhood, every field-extended fibre is
   covered, after a surjection, by irreducible subsets preserving all generic edges.
   Each graph-component union has connected image. These n images cover the fibre,
   so `lem-sfb-connected-component-maximality` bounds its component count above by n.
   For n = 0 the empty cover forces the fibre to be empty.
6. By `lem-sfb-generic-connected-component-lower-bound`, shrink so ordinary fibres
   have at least n components. The field-extension projection is surjective by
   `lem-pc-field-extension-surjective` and `lem-weil-pbc-surjective-base-change`.
   A continuous surjection maps each source component into a target component and
   hits every target component; use `lem-sfb-connected-component-maximality`.
   Thus the geometric count is at least n. Intersect the two opens to obtain equality.
7. The etale cover is open by `lem-weil-pbc-etale-morphism-open-map`; the image of
   this nonempty open is nonempty and open. Descend equality using
   `lem-weil-pbc-geometric-component-count-base-change` and return to the relative
   topology on the original Z. Take c = n; no extra hypothesis on the family is used.
-/
theorem exists_isOpen_geometricConnectedComponentCount_eq
    {Y T : Scheme.{u}} (f : Y ⟶ T) [LocallyOfFiniteType f] [QuasiCompact f]
    (Z : Set T) (hclosed : IsClosed Z) (hirreducible : IsIrreducible Z) :
    ∃ (V : Set Z) (c : ℕ∞), IsOpen V ∧ V.Nonempty ∧
      ∀ (t : Z), t ∈ V →
        ∀ (K : Type u) [Field K] [IsAlgClosed K]
          (i : T.residueField t.val ⟶ CommRingCat.of K),
          ENat.card (ConnectedComponents
            (pullback f (Spec.map i ≫ T.fromSpecResidueField t.val) : Scheme.{u})) = c := by
  sorry

end AlgebraicGeometry
