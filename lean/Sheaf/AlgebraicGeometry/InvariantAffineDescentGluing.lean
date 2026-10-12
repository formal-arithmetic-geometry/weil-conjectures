/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum

/-!
# Gluing effective affine descents

Source: Stacks Project, Descent, Tags 0AP4 and 0245;
Groupoid Schemes, proof of Tag 0H8K.
(blueprint: lem-pd-invariant-affine-descent-gluing).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace CategoryTheory.Over.DescentDatum

/-- Effective affine descents glue along a covering by transport-invariant affine opens.
Source: Stacks Project, Descent, Tags 0AP4 and 0245; proof of Tag 0H8K.
(blueprint: lem-pd-invariant-affine-descent-gluing).

Proof: The opens U in hcover cover V and are invariant in both directions, using inverse
transport. Restrict D to each U above the chosen affine B in Y. The inverse image X_B
is affine, since p is finite. Thus U -> X_B is affine, and faithfully flat affine descent
(0245) gives its effective affine model over B. The intersections of the U are invariant
open subschemes. Descent of open immersions and full faithfulness identify their descents
as open subschemes of each affine model. On triple intersections the transition maps
satisfy the cocycle condition, since they do so after base change and base change is
faithful. Glue the models along these open identifications (0AP4). The structure maps
agree on intersections, so the glued scheme lies over Y. The local pullback squares
assemble to a pullback square for V; the local invariant projections assemble to q.
They satisfy transport invariance since it holds on the covering. This gives exactly
D.IsEffective. If V is empty, glue the empty family to the empty Y-scheme. -/
theorem isEffective_of_invariant_affine_neighbourhoods
    {X Y : Scheme.{u}} {p : X ⟶ Y} [IsFinite p] [Flat p] [Surjective p]
    {V : Over X} (D : Over.DescentDatum p V)
    (hcover : ∀ v : V.left,
      ∃ U : V.left.Opens, v ∈ U ∧ IsAffineOpen U ∧
        (∃ B : Y.Opens, IsAffineOpen B ∧ U ≤ (V.hom ≫ p) ⁻¹ᵁ B) ∧
        ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p)
          (a : Over.mk f₁ ⟶ V), Set.range a.left ⊆ U →
            Set.range (D.transport f₁ f₂ h a).left ⊆ U) : D.IsEffective := by
  sorry

end CategoryTheory.Over.DescentDatum
