/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module

public import WeilConjectures.AlgebraicGeometry.DualNumbers

/-!
# First-order restriction along the diagonal

The diagonal of the dual-number thickening kills the mixed infinitesimal term.
Source: the square-zero pushout calculation in Stacks Project, Tag 0B2B,
proof of Lemma 33.16.2, applied locally over an arbitrary base ring.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry.Scheme

/-- Maps out of the product of two dual-number thickenings which agree on both axes
agree on the diagonal.
Source: Stacks Project, Tag 0B2B, proof of Lemma 33.16.2, square-zero pushout calculation.
(blueprint: lem-ag-dual-numbers-diagonal)

Proof: work locally on an affine open `Spec R` of the base. The product has algebra
`R[epsilon, delta]/(epsilon^2, delta^2)`. Both axes and the diagonal have the same
underlying space as the base. Equality on either axis therefore identifies the underlying
maps to the target. Restrict around each image point to an affine target open. The two
comorphisms have identical images modulo `delta` and modulo `epsilon`, hence their
value on any section differs by an element of `(delta) intersect (epsilon) = (epsilon*delta)`.
The equality of ideals follows by the unique expansion
`a + b*epsilon + c*delta + d*epsilon*delta`, valid over every commutative ring.
The diagonal sends both variables to the same square-zero variable, so it kills this
intersection. Thus the diagonal comorphisms agree. Equality of scheme morphisms is local
on the source, so these local equalities glue. Passing to the slice over the base preserves
this equality. No reducedness, field, smoothness, or separation assumption is used.
-/
theorem dualNumbers_diagonal_comp_eq_of_axes (S : Scheme.{u}) (X : Over S)
    (f g : dualNumbersOver S ⊗ dualNumbersOver S ⟶ X)
    (h₁ : lift (𝟙 (dualNumbersOver S))
        (toUnit (dualNumbersOver S) ≫ dualNumbersιOver S) ≫ f =
      lift (𝟙 (dualNumbersOver S))
        (toUnit (dualNumbersOver S) ≫ dualNumbersιOver S) ≫ g)
    (h₂ : lift (toUnit (dualNumbersOver S) ≫ dualNumbersιOver S)
        (𝟙 (dualNumbersOver S)) ≫ f =
      lift (toUnit (dualNumbersOver S) ≫ dualNumbersιOver S)
        (𝟙 (dualNumbersOver S)) ≫ g) :
    lift (𝟙 (dualNumbersOver S)) (𝟙 (dualNumbersOver S)) ≫ f =
      lift (𝟙 (dualNumbersOver S)) (𝟙 (dualNumbersOver S)) ≫ g := by sorry

end AlgebraicGeometry.Scheme
