/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoordinateLine.CoordinateLineConjugateExponentsGe

/-! Categorical inversion for the reverse exponent order. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory

/-- Inverting an ordered conjugate equation gives the reverse-order equation.
Source: the max-exponent cancellation in the final paragraph of
`cor-pur-affine-space-zero-section-purity.proof.md`
(blueprint: lem-route-coordinate-line-reverse-from-ordered).

Proof: compose the ordered equality on the left with the inverse of the
transition.  Associativity and the inverse-hom identity reduce the result to
`Category.comp_id`.  This is the categorical cancellation used when the order
of the two exponents is reversed. -/
theorem coordinate_line_reverse_from_ordered
    {C : Type u} [Category C] {X Y Z : C}
    (e : X ≅ Y) (u : Y ⟶ Z) (v : X ⟶ Z)
    (h : e.hom ≫ u = v) :
    e.symm.hom ≫ v = u := by
  rw [← h]
  change e.inv ≫ e.hom ≫ u = u
  simp

end
