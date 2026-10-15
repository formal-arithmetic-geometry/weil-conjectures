/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.RingTheory.DerivedCompleteModuleComplex
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Sheaf.CategoryTheory.Triangulated.DerivedLimitExistence

/-!
# Products and triangles of derived-complete module complexes

Source: Stacks Project, More on Algebra, Tags 091S and 091P
(blueprint: lem-weil-pbc-module-derived-complete-products-triangles).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace DerivedCategory

/-- Derived completeness for any ideal is preserved by countable products and satisfies
two-out-of-three in distinguished triangles of the unbounded module derived category.
Source: Stacks Project, Tag 091S, Definition 15.93.4 and the following paragraph;
Tag 091P, Lemma 15.93.2
(blueprint: lem-weil-pbc-module-derived-complete-products-triangles).

Proof:
1. Products of modules are exact: injections and kernels are checked coordinatewise,
and surjectivity follows by choosing lifts in every coordinate. Thus
`lem-weil-derived-limit-existence` supplies countable products in the unbounded derived
category and existence and isomorphism uniqueness of the multiplication-tower limits.
2. By `lem-weil-pbc-module-localization-tower-vanishing` and
`def-weil-point-derived-complete-module-complex`, completeness is equivalent to vanishing
of every map from `A[1/f][0][q]`, for every `f ∈ I` and integer `q`.
3. Each such map into a product has zero composites with all projections by completeness
of the factors. The product universal property (`def-weil-category-product`) makes the
map zero, and step 2 gives completeness of the product.
4. Shifting the source and target together shows that completeness is stable under
all integer shifts. In a distinguished triangle with complete first and third objects,
a map from `A[1/f][0][q]` to the middle object factors through the first object by
`lem-weil-pbc-hom-into-triangle-exact`, and hence is zero. Step 2 makes the middle object
complete. Rotate the triangle forward or backward using
`def-weil-triangulated-category` to obtain the other two cases.

The first conjunct asserts existence of the product, followed by completeness for any
choice of product structure. Index `n : ℕ` denotes the paper's positive index `n + 1`.
No finite-generation, boundedness, or product-existence hypothesis is imposed. -/
theorem isDerivedComplete_products_and_triangles {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{v} A)] (I : Ideal A) :
    (∀ (K : ℕ → DerivedCategory (ModuleCat.{v} A)),
      (∀ n : ℕ, IsDerivedComplete I (K n)) →
        HasProduct K ∧ ∀ [HasProduct K], IsDerivedComplete I (∏ᶜ K)) ∧
    (∀ (T : Triangle (DerivedCategory (ModuleCat.{v} A))),
      T ∈ distTriang (DerivedCategory (ModuleCat.{v} A)) →
        (IsDerivedComplete I T.obj₁ → IsDerivedComplete I T.obj₂ →
          IsDerivedComplete I T.obj₃) ∧
        (IsDerivedComplete I T.obj₁ → IsDerivedComplete I T.obj₃ →
          IsDerivedComplete I T.obj₂) ∧
        (IsDerivedComplete I T.obj₂ → IsDerivedComplete I T.obj₃ →
          IsDerivedComplete I T.obj₁)) := by
  sorry

end DerivedCategory
