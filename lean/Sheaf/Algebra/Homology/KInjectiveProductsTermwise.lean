/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Algebra.Homology.KInjectiveProducts
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective

/-! # Statements of the new targets (batch 2) about `KInjectiveProducts`

Kept in their own module so that `Sheaf.Algebra.Homology.KInjectiveProducts`, which the first task's targets use, is unchanged.
-/

@[expose] public section

universe t u v w

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- The termwise product of a family of K-injective complexes is K-injective and, with the
images of its projections, is a product in the derived category.
Source: Stacks Project, Tag 0BK6, Lemma 13.31.5
(blueprint: lem-pc-ringed-space-product-kinjective).

The degreewise product assumption is expressed as existence of the limits of the discrete
family after evaluation in each integer degree. Mathlib's `coneOfHasLimitEval` constructs
exactly the termwise product complex, with its induced differentials and projections.
K-injectivity is Mathlib's `IsKInjective` convention, and the chosen localization universe
is that of `HasDerivedCategory`.

Proof plan (Tag 0BK6; `def-sp-kinjective-bridge`, `def-weil-category-product`, and
`lem-weil-pbc-kinjective-hom-derived`):
1. Write `P` for the termwise product cone. For an acyclic complex `K` and a map
   `f : K ⟶ P.pt`, each composite with a projection is null-homotopic by K-injectivity
   of the corresponding `I t`. Choose these homotopies and assemble their components
   using the product universal property in every degree. The homotopy identities hold
   after every projection, hence hold in the product. Thus `f` is null-homotopic and
   `P.pt` is K-injective. This is the bridge's K-injectivity convention; shifting `K`
   identifies it with the acyclic Hom-complex convention in the source.
2. The image of `P` in the homotopy category is a product: choose representatives of
   a family of homotopy classes and assemble their chain maps using the termwise
   products. Two maps have equal projected classes precisely when their component
   homotopies assemble to a homotopy, as in step 1. This proves existence and uniqueness
   of the required homotopy class. It is the degreewise-product argument underlying
   `HomotopyCategory.isLimitFanQuotient` in the node's proof record; use the products
   assumed here rather than requiring products of all families in `C`.
3. Apply `CochainComplex.IsKInjective.Qh_map_bijective`, the comparison recorded by
   `lem-weil-pbc-kinjective-hom-derived`, to `P.pt` and every `I t`. Essential
   surjectivity of `DerivedCategory.Qh` lets one represent an arbitrary derived-category
   cone point in the homotopy category. The Hom bijections lift its legs, transport
   the product lift from step 2, and give uniqueness. Finally
   `DerivedCategory.quotientCompQhIso` identifies this cone with
   `DerivedCategory.Q.mapCone P`. This proves the second conjunct for the actual
   localized projections, with no K-injective resolution of the cone point required.
-/
theorem termwise_product_isKInjective_and_isLimit
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {T : Type t} (I : T → CochainComplex C ℤ) [∀ s : T, (I s).IsKInjective]
    [∀ n : ℤ, HasLimit (Discrete.functor I ⋙ HomologicalComplex.eval C (ComplexShape.up ℤ) n)] :
    IsKInjective (HomologicalComplex.coneOfHasLimitEval (Discrete.functor I)).pt ∧
      Nonempty (IsLimit (DerivedCategory.Q.mapCone
        (HomologicalComplex.coneOfHasLimitEval (Discrete.functor I)))) := by
  sorry

end CochainComplex

