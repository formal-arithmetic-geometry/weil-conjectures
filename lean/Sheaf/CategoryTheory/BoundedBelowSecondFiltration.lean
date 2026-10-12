/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Sheaf.CategoryTheory.DoubleComplexTotal
public import Sheaf.Algebra.Homology.FilteredComplexSubquotients

/-! # The second filtration for a double complex supported in a half-plane

Source: Stacks Project, Tags 012Z and 0132.
(blueprint: lem-sp-bounded-below-second-filtration).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex₂

/-- The second filtration assembles into subcomplexes and has degreewise bounds.
Source: Stacks Project, Tags 012Z and 0132; blueprint thm-sp-if-e1, proof paragraph 1.
(blueprint: lem-sp-bounded-below-second-filtration).

Proof.
For total degree n the nonzero summands have first index i nonnegative and second
index j at least b, with i+j=n. Thus b ≤ j ≤ n. For each p take the sum of the
images of the diagonal inclusions with j in [p,n]. On a diagonal summand the
horizontal differential preserves j and the vertical differential raises j by one.
Both therefore factor through the next degree's step. Their signed sum does too.
Choose these factorizations through the monomorphisms representing the steps.
The equations for the squares of the differentials and the inclusion morphism
follow by cancellation of those monomorphisms. This gives a subcomplex for each p.
The inclusions of the image sums for p ≤ q give compatible inclusions of the
subcomplexes, hence an antitone family of subobjects of the total complex.
Evaluation of its inclusions has exactly the stated images.
At p=b every nonzero diagonal summand occurs, so the coproduct universal property
makes the image sum top. At p=n+1 the indexing interval is empty, so it is bottom.
If n<b the total itself is zero, and these same equalities still hold. -/
theorem boundedBelow_secondFiltration
    {C : Type u} [Category.{v} C] [Abelian C]
    (J : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [J.HasTotal (ComplexShape.up ℤ)]
    (b : ℤ)
    (hzero : ∀ i j : ℤ, i < 0 ∨ j < b → IsZero ((J.X i).X j)) :
    ∃ L : DecreasingFiltration (J.total (ComplexShape.up ℤ)),
      (∀ p n : ℤ, L.complexStep p n = (J.secondFiltration n).step p) ∧
      (∀ n : ℤ, L.complexStep b n = ⊤) ∧
      (∀ n : ℤ, L.complexStep (n + 1) n = ⊥) := by sorry

end HomologicalComplex₂
