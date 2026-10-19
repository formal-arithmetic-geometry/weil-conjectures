/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q70
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.SixFunctors.ClassicalDefinition
public import Sheaf.AlgebraicGeometry.ClassicalDerivedDefinitions
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction

import Sheaf.AlgebraicGeometry.ClassicalDerivedEquivalence
import Sheaf.AlgebraicGeometry.ProEtaleClassicalBounds
import Sheaf.SixFunctors.UnboundedClassicalTruncation
import WeilConjectures.Algebra.Homology.BoundedBelowInjectiveResolution
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.AlgebraicGeometry.BoundedBelowProEtaleComparison
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheaves
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison

/-!
# Classical essential image of unbounded finite-coefficient comparison

Source: Bhatt--Scholze, The pro-etale topology for schemes, Proposition 5.2.6(3),
Remark 5.2.8, Definition 5.3.1 and Proposition 5.3.2; blueprint
`sec-six-functors-basics/sk-lem-geo-affine-local`, opening proof paragraph
(blueprint: lem-sfb-finite-classical-unbounded-comparison).

We use fixed-ring module sheaves, the ordinary constant-coefficient presentation.
The recorded `finiteCoefficientRealization` identifies these with modules over the
continuous-function coefficient sheaf. Classicality is the existing continuity-map
predicate `IsClassicalComplexFor`, degree by degree on cohomology sheaves.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- Exact inverse image has classical cohomology, and the canonical unbounded derived
counit is invertible on every classical complex. Consequently every such complex is
isomorphic to an inverse image, without any boundedness or constructibility condition.
Source: Bhatt--Scholze, Proposition 5.2.6(3), Remark 5.2.8 and Proposition 5.3.2,
and the opening comparison in blueprint `sk-lem-geo-affine-local`
(blueprint: lem-sfb-finite-classical-unbounded-comparison).

Proof:
1. By lem-weil-pbc-exact-functor-bounded-below, termwise exact inverse image
commutes with every cohomology sheaf. By sk-thm-pe-classical-sheaves, its sheaf
image is classical. Thus its entire unbounded derived image has classical cohomology.
2. For empty X both sheaf categories are zero. Otherwise set e = 2 dim X + 1.
Every A-module is torsion since ell^r kills A. Apply
det-pe-unbounded-classical-bounds to the identity and the constant presentation of
an affine etale W. The classical essential image of sk-thm-pe-classical-sheaves
extends this uniform bound to every classical module sheaf on W.
3. The unit from sk-prop-sf-comparison and det-pe-classical-derived-equivalence
give the bounded-below counit. By lem-sc-bounded-below-injective-resolution,
bounded-below injective resolutions are K-injective and compute the same counit.
4. By prop-pur-kinjective-resolutions-exist choose a K-injective resolution I of K.
By lem-weil-pbc-kinjective-total-derived, derived evaluation at W is computed by
I(W), and direct image is restriction to etale objects. Exact module sheafification
(lem-weil-pbc-site-module-presheaf-sheafification-exact) therefore identifies
H^m(R nu_* K) with the sheafification of W |-> H^m R Gamma(W,K).
This identification is natural: lem-weil-pbc-kinjective-hom-derived represents
maps between resolutions by chain maps, uniquely up to homotopy.
5. Fix m and choose N < m - e - 1. The truncation T = tau_{>=N} K is bounded
below and classical. By det-pe-unbounded-classical-truncation(2), K -> T induces
an isomorphism on degree-m derived sections of every affine etale W. The kernels
and cokernels of the resulting presheaf map vanish on these objects; affine open
covers and the sheaf condition make their sheafifications zero. Step 4 gives
that H^m(R nu_* K) -> H^m(R nu_* T) is invertible. Exact inverse image preserves
this isomorphism. Counit naturality, the bounded-below counit from step 3 and
H^m(K) = H^m(T) now make H^m of the actual counit at K invertible.
Vary m and apply lem-weil-pbc-unbounded-derived-iso-cohomology.
6. Take M = R nu_* K and the isomorphism supplied by its counit for the final clause. -/
theorem finiteClassicalUnboundedComparison
    (k : Type u) [Field k] (hbase : Finite k ∨ IsAlgClosed k)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (algebraMap ℤ k (ℓ : ℤ)))
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ∃ r : ℕ, 1 ≤ r ∧ (ℓ : A) ^ r = 0)
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))] :
    (∀ M : FiniteCoefficientEtaleDerivedCategory X A,
      IsClassicalComplexFor X A
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj M)) ∧
    (∀ K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)),
      IsClassicalComplexFor X A K →
        IsIso
          ((comparisonAdjunction (ModuleCat.{u + 1} A) X).mapDerivedCategoryRightDerivedAdjunction
            |>.counit.app K)) ∧
    (∀ K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)),
      IsClassicalComplexFor X A K →
        ∃ M : FiniteCoefficientEtaleDerivedCategory X A,
          Nonempty
            ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj M ≅ K)) := by
  sorry

end AlgebraicGeometry.ProEtale
