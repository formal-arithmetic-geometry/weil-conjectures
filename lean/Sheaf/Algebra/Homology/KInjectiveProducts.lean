/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.CategoryTheory.KInjectiveBridge

/-!
# Termwise products of K-injective complexes

Source: Stacks Project, Derived Categories, Lemma 13.31.5, Tag 0BK6
(blueprint: lem-pc-ringed-space-product-kinjective).
-/

universe w v u t

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- The termwise product of a family of K-injective complexes is K-injective and, with the
images of its projections, is a product in the derived category.
Source: Stacks Project, Tag 0BK6, Lemma 13.31.5
(blueprint: lem-pc-ringed-space-product-kinjective).

The degreewise product assumption is expressed as existence of the limits of the discrete
family after evaluation in each integer degree. Mathlib's `coneOfHasLimitEval` constructs
exactly the termwise product complex, with its induced differentials and projections.
K-injectivity is the `IsKInjective` convention of `def-sp-kinjective-bridge`; the chosen
localization universe is that of `def-weil-abstract-derived-category`.

Proof:
1. For an acyclic complex `K`, its Hom complex into the termwise product is the product of
   the Hom complexes into the factors. Each factor is acyclic by K-injectivity
   (`def-sp-kinjective-bridge`). Exactness of products of abelian groups
   (`lem-pc-abelian-groups-exact-products`) makes the product Hom complex acyclic, so the
   termwise product is K-injective.
2. Chain maps into the product, and homotopies between such maps, are precisely families
   of maps and homotopies into the factors. Thus the same projections have the product
   universal property in the homotopy category.
3. Maps from acyclic complexes into the factors and the product are null-homotopic by
   Step 1. The K-injective Hom comparison (`lem-weil-pbc-kinjective-hom-derived`) identifies
   morphisms into their images in the derived category with homotopy-category morphisms.
   Step 2 therefore gives the product universal property (`def-weil-category-product`) in
   the derived category, with the images of the very same projections. -/
theorem termwise_product_isKInjective_and_isLimit
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {T : Type t} (I : T → CochainComplex C ℤ) [∀ s : T, (I s).IsKInjective]
    [∀ n : ℤ, HasLimit (Discrete.functor I ⋙ HomologicalComplex.eval C (ComplexShape.up ℤ) n)] :
    let P := HomologicalComplex.coneOfHasLimitEval (Discrete.functor I)
    IsKInjective P.pt ∧ Nonempty (IsLimit (DerivedCategory.Q.mapCone P)) := by
  sorry

end CochainComplex
