/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q36
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison
public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Sheaf.Paper.ProEtaleConstructibleSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.Paper.FiniteRingConstructibleSheafOrigin
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.CategoryTheory.Triangulated.Triangulated
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules

/-!
# Bounded constructible derived comparison for arbitrary finite rings

Source: Stacks Project, Tag 09AL, lemma-compare-constructible-derived, and its exact
cohomology comparison, with the blueprint's global finite-stratification convention
(blueprint: lem-weil-pbc-finite-ring-constructible-derived-origin).

The induced equivalence is stated by its equivalent full-faithfulness and essential-image
criterion. The functor is the specified exact inverse image, in the canonical constant-ring
presentation used by intrinsic constructibility. Its source is the existing full bounded
constructible etale subcategory. The essential-image criterion includes the etale-origin
conclusion, without choosing an inverse equivalence.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Exact inverse image induces an equivalence from bounded constructible etale complexes
onto the pro-etale complexes with intrinsically constructible bounded cohomology, and
preserves and reflects every cohomological interval. Fullness, faithfulness and the
specified essential image are the standard criterion for this induced equivalence.
The ring is any finite commutative ring, including the zero ring; no valuation ring is used.
Source: Stacks Project, Tag 09AL, with the global finite partitions of the blueprint
(blueprint: lem-weil-pbc-finite-ring-constructible-derived-origin).

Proof (the node's seven steps):
1. A finite ring is Noetherian because its ideals form a finite set. Apply
`lem-weil-pbc-finite-ring-constructible-sheaf-origin` for the equivalence of globally
constructible sheaves. Keep their finite global partitions throughout.
2. Exactness from `prop-weil-pbc-site-comparison-finite-level` identifies the cohomology
of termwise inverse image with inverse image of cohomology. The induced functor commutes
with shifts and preserves triangles by `lem-sf-exact-functor-derived-triangulated`.
Full faithfulness on bounded below complexes from `thm-weil-pbc-site-comparison` restricts
to the bounded constructible subcategory.
3. If all cohomology vanishes, the complex is zero in the localization and has zero etale
origin. Otherwise induct on the width of its bounding interval. In width zero,
`lem-sf-derived-concentrated-single` identifies the object with its sole cohomology sheaf,
shifted to the specified degree. Lift that sheaf by the sheaf comparison and use shift
and single-complex compatibility of exact derived inverse image.
4. For width greater than zero, `lem-sf-derived-truncation-triangle` splits off the top
cohomological degree. The long exact sequence from
`lem-sf-derived-homology-long-exact` identifies the lower truncation's cohomology below
the top degree and the upper truncation's cohomology at the top degree. Both truncations
are globally constructible with the required smaller intervals; apply induction.
5. Full faithfulness on bounded below complexes lifts the connecting arrow between these
origins. TR1 and inverse rotation TR2 produce its cone triangle. Exact inverse image
preserves that triangle. Rotate twice and apply TR3 to the identity maps on its outer
terms; `lem-sf-triangle-morphism-iso` makes the remaining map invertible. Inverse shift
therefore identifies the image of the etale cone with the original pro-etale object.
6. Exact cohomology comparison and the underived unit reflect the vanishing outside the
original interval. The sheaf equivalence reflects constructibility of each cohomology
sheaf, so the etale cone is bounded constructible. This proves the essential-image
criterion, whose forward direction follows from step 2.
7. For any etale complex, exact cohomology comparison preserves vanishing in every degree;
the underived unit reflects it. Apply this degreewise outside any interval, including an
empty interval. The coefficient realization is the canonical sheafification along the
constant-scalar unit, so these statements concern the specified inverse image in the
intrinsic constant-ring presentation. -/
theorem finiteRing_constructibleDerived_origin (X : Scheme.{u})
    (B : Type u) [CommRing B] [Finite B] :
    (ObjectProperty.ι (Etale.DerivedCategory.isBoundedConstructible
        (ULift.{u + 1, u} B) X) ⋙
      ProEtale.finiteCoefficientIntrinsicDerivedComparison X B).Full ∧
    (ObjectProperty.ι (Etale.DerivedCategory.isBoundedConstructible
        (ULift.{u + 1, u} B) X) ⋙
      ProEtale.finiteCoefficientIntrinsicDerivedComparison X B).Faithful ∧
    (∀ K : proEtaleDerivedCategory X B,
      (ObjectProperty.ι (Etale.DerivedCategory.isBoundedConstructible
          (ULift.{u + 1, u} B) X) ⋙
        ProEtale.finiteCoefficientIntrinsicDerivedComparison X B).essImage K ↔
      (∀ i : ℤ, IsConstructibleProEtaleModuleSheaf X B
        ((DerivedCategory.homologyFunctor
          (proEtaleRingModules X (proEtaleConstantRing X B)) i).obj K)) ∧
      ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) →
        IsZero ((DerivedCategory.homologyFunctor
          (proEtaleRingModules X (proEtaleConstantRing X B)) i).obj K)) ∧
    (∀ (L : ProEtale.FiniteCoefficientEtaleDerivedCategory X (ULift.{u + 1, u} B))
      (a b : ℤ),
      (∀ i : ℤ, (i < a ∨ b < i) →
        IsZero ((DerivedCategory.homologyFunctor
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) i).obj L)) ↔
      (∀ i : ℤ, (i < a ∨ b < i) →
        IsZero ((DerivedCategory.homologyFunctor
          (proEtaleRingModules X (proEtaleConstantRing X B)) i).obj
            ((ProEtale.finiteCoefficientIntrinsicDerivedComparison X B).obj L)))) := by
  sorry

end AlgebraicGeometry.Scheme
