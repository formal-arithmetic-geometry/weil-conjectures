/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Right derived functors and finite products

Source: `literature/stacks-project/etale-cohomology.tex`, first paragraph of
Lemma 0A5B (finite-product assembly; derived-functor formulation supplied
explicitly) (blueprint: lem-weil-pbc-derived-finite-product).
-/

universe u v w z

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Right derived functors commute with a finite componentwise product.

The functor `Γ` is `Functor.pi Γi ⋙ Pi.functor I`; the right hand side is
the same construction applied to `(Γi i).rightDerived q`. The conclusion
supplies the product-category structures and additivity needed to form its
right derived functors, together with left exactness. This is the
finite-product assembly statement used in the proof of Lemma 0A5B.

Proof source: Section 0156 of `derived.tex` and the finite-product
cohomology calculation; choose componentwise injective resolutions, form their
product resolution using `lem-weil-pbc-finite-product-injective-resolutions`.
The functor is additive and left exact by
`lem-weil-pbc-finite-product-functor-left-exact`. Apply it degreewise to the
product resolution, and identify the resulting cohomology componentwise using
`lem-weil-pbc-finite-product-complex-cohomology`. The two sides compute the
right derived functors by `def-sp-left-exact-additive` and
`def-sp-injective-resolutions`. Coordinate projections induce the comparison,
so it is natural in the family and its morphisms.
(blueprint: lem-weil-pbc-derived-finite-product) -/
theorem rightDerived_finite_product
    (I : Type u) [Finite I]
    (A : I → Type v) [∀ i, Category.{w} (A i)] [∀ i, Abelian (A i)]
    [∀ i, HasInjectiveResolutions (A i)]
    (Γi : (i : I) → A i ⥤ AddCommGrpCat.{z})
    [∀ i, (Γi i).Additive] [∀ i, PreservesFiniteLimits (Γi i)] :
    let Γ := Functor.pi Γi ⋙ Pi.functor I
    ∃ hAb : Abelian (∀ i, A i),
      letI := hAb
      ∃ hRes : HasInjectiveResolutions (∀ i, A i),
        ∃ hAdd : Γ.Additive,
          PreservesFiniteLimits Γ ∧
            (letI := hRes
             letI := hAdd
             ∀ q : ℕ, Nonempty (Γ.rightDerived q ≅
               Functor.pi (fun i ↦ (Γi i).rightDerived q) ⋙ Pi.functor I)) := by
  sorry

end CategoryTheory
