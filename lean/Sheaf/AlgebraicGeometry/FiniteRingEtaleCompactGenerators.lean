/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import Sheaf.CategoryTheory.CompactObject
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

import Sheaf.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Sheaf.AlgebraicGeometry.OpenClosedRecollement
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.SixFunctors.FlatModel
import Sheaf.CategoryTheory.CompactCone
import Sheaf.AlgebraicGeometry.EtaleLowerShriekConstantConstructible
import Sheaf.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroFlat
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# Compact generators on finite-type étale sites

Source: Bhatt--Scholze, *The pro-étale topology for schemes*, Section 6.4,
hypothesis before Example 6.4.1, Example 6.4.1, Lemmas 6.4.2 and 6.4.5,
and Proposition 6.4.8 (blueprint: lem-pur-etale-finite-ring-compact-generators).

Coproducts and the generator set are indexed in universe `u + 1`, the universe of the
module values and the small presentation of the site. The derived category has objects
in universe `u + 2`, but this does not enlarge the universe of its available coproducts.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Bounded constructible finite-Tor complexes on a finite-type scheme over an algebraically
closed field are compact in the full unbounded étale derived category, and a set of these
complexes detects isomorphisms. No separatedness is required.

Proof, following the node and Bhatt--Scholze, Section 6.4:
1. A field is Noetherian, so `lem-weil-pbc-finite-type-over-noetherian` and
   `lem-weil-pbc-locally-noetherian-quasi-separated` make `T` qcqs.
   `lem-weil-pbc-module-sheaves-grothendieck-abelian`, `def-weil-size-convention`,
   `prop-pur-kinjective-resolutions-exist`, `lem-pc-derived-category-locally-small`, and
   `lem-kun-grothendieck-derived-coproducts` give local smallness and termwise coproducts,
   including the empty coproduct, in the module-value indexing universe.
2. `lem-pur-etale-lisse-stratum-compact` makes the extensions of finite locally constant
   flat sheaves from locally closed strata compact. Closed direct image is exact by
   `lem-cbc-open-closed-recollement`, and `lem-weil-pbc-exact-functor-derived-functor`
   identifies its derived and termwise forms used by `sk-lem-sf-flat-model`.
3. Compact objects are closed under shifts, cones (`lem-sc-compact-cone`), retracts,
   isomorphisms, and zero. The Noetherian complement of `sk-lem-sf-flat-model` places
   every bounded constructible finite-Tor complex in the thick subcategory of the
   preceding stratum objects. This proves the first compactness assertion.
4. Choose representatives of an affine étale basis using
   `lem-weil-pbc-affine-etale-essentially-small-cover`. Its free extensions `u_! C[0]`
   are constructible by `lem-weil-pbc-etale-free-sheaf-constructible` and flat by
   `lem-pc-sites-modules-j-shriek-flat`. They have Tor amplitude `[0,0]` by the K-flat
   description in `def-kun-derived-tensor`, hence satisfy the required conditions.
5. `def-weil-presheaf-modules-sheafification` and
   `lem-weil-pbc-free-yoneda-presheaf-module` identify maps from these free sheaves with
   sections. On a K-injective representative `I`, `lem-weil-pbc-kinjective-hom-derived`
   identifies maps from their shifts with `H^(-n)(I(U))`, naturally in the target.
6. Represent `h` between K-injectives (`prop-pur-kinjective-resolutions-exist` and
   `lem-weil-pbc-kinjective-hom-derived`). The assumed bijections give bijections on
   section cohomology at every affine basis object. Local cocycle representatives and
   local boundaries then give surjectivity and injectivity on every cohomology sheaf.
   The representing chain map is a quasi-isomorphism, so `h` is invertible by
   `def-weil-abstract-derived-category`.

Source: Bhatt--Scholze, Section 6.4, Example 6.4.1, Lemmas 6.4.2 and 6.4.5, and
Proposition 6.4.8; perfect-value constructibility is related to bounded constructibility
and finite Tor amplitude by Lemma 6.3.7 and the finite-Tor perfectness criterion.
(blueprint: lem-pur-etale-finite-ring-compact-generators) -/
theorem finiteRing_compactGenerators
    {k : Type u} [Field k] [IsAlgClosed k]
    (ℓ : ℕ) (hℓprime : Nat.Prime ℓ) (hℓunit : IsUnit (ℓ : k))
    {T : Scheme.{u}} (f : T ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] [QuasiCompact f]
    {C : Type (u + 1)} [CommRing C] [Finite C]
    (hC : ∃ n : ℕ, (ℓ : C) ^ n = 0) :
    ∃ (hcoprod : HasCoproducts.{u + 1} (DerivedCategoryModule C T)),
      LocallySmall.{u + 1} (DerivedCategoryModule C T) ∧
      (∀ E : DerivedCategoryModule C T,
        DerivedCategory.isBoundedConstructible C T E ∧
          (∃ r s : ℤ, r ≤ s ∧ DerivedCategory.hasTorAmplitudeIn C T r s E) →
        @IsCompactObject (DerivedCategoryModule C T) _ _ hcoprod E) ∧
      (∃ (S : Type (u + 1)) (E : S → DerivedCategoryModule C T),
        (∀ s : S, DerivedCategory.isBoundedConstructible C T (E s) ∧
          ∃ r t : ℤ, r ≤ t ∧ DerivedCategory.hasTorAmplitudeIn C T r t (E s)) ∧
        ∀ (A B : DerivedCategoryModule C T) (h : A ⟶ B),
          (∀ (s : S) (n : ℤ),
            Function.Bijective (fun (φ : (E s)⟦n⟧ ⟶ A) ↦ φ ≫ h)) → IsIso h) := by
  sorry

end AlgebraicGeometry.Etale
