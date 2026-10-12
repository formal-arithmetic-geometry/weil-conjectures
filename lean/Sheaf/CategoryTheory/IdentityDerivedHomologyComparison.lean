/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Identity functor and the derived homology comparison

Source: the canonical localization constructions in ExactFunctor.lean.
(blueprint: lem-weil-pbc-identity-derived-homology-comparison)
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Functor

/-- The homology comparison of the identity functor is homology of its inverse
canonical derived identity comparison.

Source: Stacks Project, Tag 01F8, equation 01FA; the localization constructions
`mapDerivedCategoryHomologyFunctorIso` and `mapDerivedCategoryPlusIdIso`.
(blueprint: lem-weil-pbc-identity-derived-homology-comparison)

Proof: on complexes the identity functor acts as identity on kernels, cokernels,
and hence homology. The induced homology comparison is therefore homology of the
canonical comparison of the complex mapped by identity with the original complex.
The localization factorization equations transport this equality to the derived
category: equality of natural transformations can be checked after precomposition
with the localization functor. Restrict the resulting natural-transformation
identity along the fully faithful inclusion of bounded below derived objects.
The bounded below compatibility isomorphisms cancel and give the displayed
formula. All degrees and all bounded below objects are allowed. -/
/- Core identity comparison on the unbounded derived category.

Source: Stacks Project, Tag 01F8, equations 01F9--01FA.
The identity exact functor induces the identity on homology, and the
localization construction identifies this with the inverse of the canonical
derived identity isomorphism.
(blueprint: lem-weil-pbc-identity-derived-homology-comparison-core) -/
theorem identityDerivedHomologyComparisonCore {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (n : ℤ) (X : DerivedCategory C) :
    ((𝟭 C).mapDerivedCategoryHomologyFunctorIso n).hom.app X =
      (DerivedCategory.homologyFunctor C n).map
        ((mapDerivedCategoryIdIso C).inv.app X) := by
  sorry

/-- Compatibility of the bounded-below homology functor with the fully faithful inclusion.

Source: Stacks Project, Tag 01F8, equations 01F9--01FA.
The homology map of the preimage under the bounded-below inclusion is the
composite of the homology map and the compatibility inverse.
(blueprint: lem-weil-pbc-identity-derived-homology-comparison-compatibility) -/
theorem identityDerivedHomologyComparisonCompatibility {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (n : ℤ) (K : DerivedCategory.Plus C) :
    (DerivedCategory.homologyFunctor C n).map
        (DerivedCategory.Plus.ι.preimage
          ((mapDerivedCategoryIdIso C).inv.app K.obj ≫
            (𝟭 C).mapDerivedCategoryPlusCompatibility.inv.app K)).hom =
      (DerivedCategory.homologyFunctor C n).map ((mapDerivedCategoryIdIso C).inv.app K.obj) ≫
        (DerivedCategory.homologyFunctor C n).map
          ((𝟭 C).mapDerivedCategoryPlusCompatibility.inv.app K) := by
  sorry

theorem identityDerivedHomologyComparison {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (n : ℤ) (K : DerivedCategory.Plus C) :
    ((𝟭 C).mapDerivedCategoryPlusHomologyFunctorIso n).hom.app K =
      (DerivedCategory.Plus.homologyFunctor C n).map
        ((mapDerivedCategoryPlusIdIso C).inv.app K) := by
  have h := identityDerivedHomologyComparisonCore n (DerivedCategory.Plus.ι.obj K)
  have h' := congrArg (fun f ↦ f ≫
      (DerivedCategory.homologyFunctor C n).map
        ((𝟭 C).mapDerivedCategoryPlusCompatibility.inv.app K)) h
  simpa [mapDerivedCategoryPlusHomologyFunctorIso, mapDerivedCategoryPlusIdIso,
    Functor.map_comp, DerivedCategory.Plus.homologyFunctor,
    DerivedCategory.Plus.ι.map_preimage, Functor.map_preimage,
    identityDerivedHomologyComparisonCompatibility] using h' 

end CategoryTheory.Functor
