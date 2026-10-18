/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q67
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Sheaf.Algebra.Homology.KInjectiveRestrictLocalized
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Sheaf.AlgebraicGeometry.AbelianEtaleProEtaleCohomologyComparison
import Sheaf.AlgebraicGeometry.EtaleModuleCohomologyForget
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
import Sheaf.AlgebraicGeometry.ComparisonGlobalCohomologyFiniteNormalized
import Sheaf.CategoryTheory.DerivedCategory.FiniteCDDerivedUpperBound
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit

import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Sheaf.AlgebraicGeometry.EtaleModuleAffineBound
import Sheaf.AlgebraicGeometry.InjectiveComplexSliceSectionModel
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import Sheaf.SixFunctors.ClassicalModuleAffineEvaluationBound
import Sheaf.SixFunctors.UnboundedClassicalTruncation
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
set_option autoImplicit false

/-!
# Unbounded comparison on the small etale and pro-etale sites

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
`sk-prop-pe-unbounded-classical/sk-prop-pe-unbounded-classical-unit.md`
(blueprint: lem-sfb-unbounded-site-comparison).

The theorem states exactness, full faithfulness, and arbitrary small-coproduct preservation
of the canonical finite-coefficient comparison on unbounded derived categories.
-/


@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- For a finite or algebraically closed field and a finite primary coefficient ring, the
termwise comparison from the etale to the pro-etale module derived category is exact,
fully faithful, and preserves arbitrary small direct sums.

Source: blueprint `sk-prop-pe-unbounded-classical/sk-prop-pe-unbounded-classical-unit.md`,
statement and proof (blueprint: lem-sfb-unbounded-site-comparison).
Proof:
1. Write L for comparison inverse image and R for direct image on module sheaves.
By det-pe-classical-sheaves-modules, L is exact with classical essential image.
By lem-sf-exact-functor-derived-triangulated it induces the triangulated termwise
functor. The kernel/image computation of lem-weil-pbc-exact-functor-complex-cohomology
identifies H^q(LK) with L(H^q K), and L commutes with canonical truncations.
2. Use prop-pur-kinjective-resolutions-exist and lem-weil-pbc-kinjective-total-derived
to construct the unbounded right derived functor of R. Its homotopy functor is exact,
since R preserves finite biproducts, shifts and cones. By
lem-weil-pbc-right-adjoint-preserves-kinjective, R sends K-injectives to K-injectives.
The Hom bijections of lem-weil-pbc-kinjective-hom-derived and
lem-weil-pbc-termwise-adjunction-homotopy give L adjoint to the derived R. Its unit
is represented by P -> RLP -> RJ for a K-injective resolution LP -> J.
3. Choose a K-injective I representing K and a resolution LI -> J, with adjoint
f : I -> RJ. Restrict to an affine etale W using lem-pur-kinjective-restrict-localized,
lem-weil-pbc-etale-inverse-image-restriction and
lem-weil-proetale-weakly-etale-localization. Slice restriction is exact, since local
lifts of sections stay over W. By lem-weil-pbc-comparison-pullback, (LI)|W = L(I|W).
Evaluation I(W) and J(W) computes the two derived sections. The definition of direct
image identifies f(W) with their canonical comparison, naturally in K and W.
4. If X is empty, both module categories and derived categories are zero. Otherwise
put e = 2 dim X + 1. Every module sheaf is torsion because a power of ell kills A.
Apply det-pe-unbounded-classical-bounds (1) with the identity and constant presentation
of W. The abelian comparison lem-cbc-abelian-etale-proetale-cohomology-comparison and
lem-weil-pbc-etale-module-cohomology-forget give the etale module cohomology bound e.
By exact restriction and lem-weil-pbc-etale-restriction-injectives, evaluating an
injective resolution computes this cohomology, so evaluation on X has derived bound e.
The bounded-below comparison lem-weil-pbc-comparison-global-cohomology gives the same
bound on pro-etale classical modules, since each is LG by det-pe-classical-sheaves-modules.
5. Fix m and N < m - e - 1. Apply lem-sf-finite-cd-derived-upper-bound (Stacks 07K7)
to the canonical truncation triangle of def-sbc-standard-tstructure-derived-category.
Derived sections of the lower truncation vanish in degrees m and m+1. Thus
lem-sf-derived-homology-long-exact makes the degree-m etale truncation map invertible.
On the pro-etale side use det-pe-unbounded-classical-truncation (2), since LK has
classical cohomology and the bound from step 4. Identify the truncations by step 1.
6. The square of degree-m comparisons for K and its lower-bounded truncation commutes
by naturality. The vertical maps are invertible by step 5; the lower comparison is
invertible by lem-weil-pbc-comparison-global-cohomology. Thus H^m(f(W)) is invertible.
7. By lem-weil-pbc-site-r-module-presheaf-sheafification-exact, sheafifying the
presheaves H^m(I(W)) and H^m(J(W)) gives H^m(I) and H^m(RJ). This follows by sheafifying
the sectionwise kernel/image quotient. The affine etale objects are cover-dense by
lem-weil-pbc-affine-etale-essentially-small-cover, so step 6 makes H^m(f) invertible.
By lem-weil-pbc-unbounded-derived-iso-cohomology the unbounded unit is invertible.
8. The adjunction sends the map L(u) to composition of u with the invertible unit,
so L is fully faithful. The module categories are Grothendieck by
lem-weil-pbc-ring-sheaves-grothendieck. Their unbounded derived coproducts exist by
lem-kun-grothendieck-derived-coproducts, including the empty one. The derived adjunction
and lem-weil-pbc-left-adjoint-preserves-colimits give preservation of these coproducts.
Together with step 1 this proves all three assertions.
-/
theorem unboundedSiteComparison
    (k : Type u) [Field k] (hbase : Finite k ∨ IsAlgClosed k)
    {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓ : IsUnit (algebraMap ℤ k (ℓ : ℤ)))
    (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A]
    (hA : ∃ n : ℕ, (ℓ : A) ^ n = 0)
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))] :
    (finiteCoefficientComparison X A).mapDerivedCategory.IsTriangulated ∧
      Nonempty (finiteCoefficientDerivedComparison X A).FullyFaithful ∧
      ∀ (I : Type v),
        Nonempty (PreservesColimitsOfShape (Discrete I)
          (finiteCoefficientDerivedComparison X A)) := by
  sorry

end AlgebraicGeometry.ProEtale
