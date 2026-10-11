/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Geometric connectedness of a fibre tested on étale neighbourhoods

Source: Stacks Project, More on Morphisms, Tag 03GZ
(blueprint: lem-weil-pbc-stein-geometric-fibre-etale-criterion).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A fibre is geometrically connected exactly when the fibre over every étale neighbourhood
of its base point is connected. Source: Stacks Project, More on Morphisms, Tag 03GZ
(blueprint: lem-weil-pbc-stein-geometric-fibre-etale-criterion).

Proof plan:
1. For an étale map `e : U ⟶ S` and a point `t` above `s`, the residue extension
   `κ(t)/κ(s)` is finite separable, by
   `lem-weil-pbc-etale-residue-field-extension-separable`. Associativity of fibre products
   identifies the fibre of the base change at `t` with the field base change of `g.fiber s`
   (using `def-pc-scheme-fibre` and `def-pc-base-change`).
2. Geometric connectedness, `def-pc-geometrically-irreducible`, makes this field base change
   connected, proving the forward implication.
3. Conversely, if the fibre is not geometrically connected,
   `lem-weil-pbc-geometrically-connected-finite-separable-test` supplies a finite separable
   residue-field extension with disconnected base change.
   `lem-weil-pbc-etale-neighbourhood-prescribed-residue-field` realizes that extension by
   an affine étale neighbourhood. The fibre identification of step 1 contradicts the
   assumed connectedness of its fibre. -/
theorem Scheme.Hom.geometricallyConnected_fiber_iff_connectedSpace_etale_neighbourhood
    {X S : Scheme.{u}} (g : X ⟶ S) (s : S) :
    GeometricallyConnected (g.fiberToSpecResidueField s) ↔
      ∀ (U : Scheme.{u}) (e : U ⟶ S) [Etale e] (t : U), e t = s →
        ConnectedSpace ((pullback.snd g e).fiber t) := by
  sorry

end AlgebraicGeometry
