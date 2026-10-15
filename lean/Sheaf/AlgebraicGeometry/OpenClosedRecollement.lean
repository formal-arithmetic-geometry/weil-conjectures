/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.Finite.Exact
import Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import WeilConjectures.SixFunctors.OpenClosed.Exact
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-!
# Functorial open-closed recollement

Source: blueprint, sec-smooth-purity/sk-prop-sf-open-closed-triangle,
lemma Open-closed recollement (blueprint: lem-cbc-open-closed-recollement).
Stacks Project, Tags 095L, 0152 and 015F.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.Etale

/-- The natural open-closed triangle on the bounded below derived category, with its
specified counit and unit (blueprint: lem-cbc-open-closed-recollement).
Source: blueprint sec-smooth-purity/sk-prop-sf-open-closed-triangle, Open-closed recollement;
Stacks Project, Tags 095L, 0152 and 015F.

Proof plan:
1. A closed immersion is finite, so its direct image is exact
(`lemma-weil-pbc-finite-direct-image-exact`). Forgetting coefficients reflects exactness by
`lem-weil-pbc-module-sheaves-colimits-forgetful`. Inverse images are exact by
`prop-weil-pbc-inverse-image-modules-exact`, and extension by zero is exact by
`lem-weil-pbc-extension-by-zero-exact`. Their termwise derived functors are identified by
`lem-weil-pbc-exact-functor-derived-functor`.
2. Apply `lem-weil-pbc-open-closed-short-exact` degreewise. Naturality of the counit and
unit makes a short exact sequence of complexes, natural in chain maps.
3. Apply `lem-weil-pbc-complex-ses-triangle`: its connecting map is natural in all three
components of a map of short exact sequences.
4. All functors preserve quasi-isomorphisms. The connecting-map identity for chain maps
therefore holds also for inverses of quasi-isomorphisms, and hence every derived morphism.
The adjunctions descend with their units and counits, using
`lem-weil-pbc-extension-by-zero-adjunction` and
`prop-weil-pbc-inverse-image-modules-exact`. Finally
`lem-weil-pbc-exact-functor-bounded-below` places all three terms and maps in the full
triangulated subcategory D⁺. -/
theorem exists_functorial_distTriang_openClosed
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X U Z : Scheme.{u}} (j : U ⟶ X) (i : Z ⟶ X)
    [IsOpenImmersion j] [IsClosedImmersion i]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    ∃ δ : ∀ K : _root_.DerivedCategory.Plus
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      (lowerStar (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus.obj
          ((upperStar (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus.obj K) ⟶
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus.obj
          ((upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus.obj K))⟦(1 : ℤ)⟧,
      (∀ K, Triangle.mk
        ((derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
          (ModuleCat.{u + 1} Λ) j).counit.app K)
        ((upperStarLowerStarAdjunction
          (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlusAdjunction.unit.app K)
        (δ K) ∈ distTriang _) ∧
      (∀ (K K' : _root_.DerivedCategory.Plus
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (f : K ⟶ K'),
        (lowerStar (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus.map
            ((upperStar (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus.map f) ≫ δ K' =
          δ K ≫ (shiftFunctor _ (1 : ℤ)).map
            ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus.map
              ((upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus.map f))) := by
  sorry

end AlgebraicGeometry.Etale
