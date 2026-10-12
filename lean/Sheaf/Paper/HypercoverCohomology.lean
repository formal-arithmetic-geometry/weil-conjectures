/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.Paper.HypercoverCohomologyColimit
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist
import Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.Paper.FiniteSplitEtaleHypercover
import Sheaf.Paper.FiniteSplitHypercoverRefinement
import Sheaf.Paper.HypercoverFreeResolution
import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex

/-!
# Derived étale cohomology computed by finite split hypercovers

Source: blueprint `sec-curve-estimates/sk-prop-h2`, order 949; Stacks Project, Tag 01H0.
(blueprint: thm-weil-pbc-hypercover-cohomology)

The natural comparison is expressed as a colimit universal property with vertex the derived
cohomology functor. This specifies the natural isomorphism without choosing a colimit object.
-/

@[expose] public section

universe u₁

open CategoryTheory

namespace AlgebraicGeometry

/-- Finite split hypercovers compute derived étale cohomology of abelian sheaves and sheaves
of modules over any fixed constant ring. Refinement maps descend to simplicial homotopy
classes. The comparison cocone is natural in the coefficient sheaf and is a colimit at each
sheaf. A cocycle uses degree `q`, its equation degree `q+1`, and a boundary witness degree
`q-1` when `q > 0`: representatives and relations therefore use finitely many degrees.

Source: blueprint order 949; Stacks Project, Theorem 25.10.1, Tag 01H0.
(blueprint: thm-weil-pbc-hypercover-cohomology)

Proof:
1. Choose an injective resolution of the coefficient sheaf, using
`prop-weil-pbc-kinjective-resolutions-exist` (and
`lem-weil-pbc-module-sheaves-enough-injectives` for module coefficients). Evaluating on a
hypercover gives the double complex `I^r(U_p)`. The augmented free hypercover resolution of
`lem-weil-pbc-hypercover-free-resolution` is exact, and applying Hom into each injective gives
exact augmented rows.
2. Filter the total complex by simplicial degree. The double-complex spectral sequences of
`thm-sp-double-complex-spectral-sequences` identify its cohomology with derived global
sections. The inclusion of `F(U_p)` into `I^0(U_p)` supplies the comparison, compatible with
refinements. Degree zero is the sheaf equalizer.
3. For surjectivity, start with a total degree-`q` cocycle. Kill its component of highest
positive vertical degree by locally lifting through the preceding injective differential,
using `lem-weil-pbc-abelian-sheaf-epi-locally-surjective` and
`lem-weil-pbc-hypercover-refinement`. Subtract the resulting total boundary and repeat. The
remaining vertical-degree-zero component belongs to `F(U_q)` and is a hypercover cocycle.
4. For injectivity, start with a hypercover cocycle that is a total boundary. Successively
kill the positive-vertical-degree components of its primitive by the same lifting and
refinement process. The remaining primitive belongs to `F(U_(q-1))`. For `q = 1` this is
already the only primitive component; for `q = 0` the inclusion into `I^0` is injective and
there are no degree-minus-one boundaries.
5. Common refinements and the prism identity of `lem-weil-pbc-hypercover-refinement` give
independence of representatives and homotopic refinement maps. Maps of injective resolutions
are unique up to homotopy, giving naturality in the sheaf. Every correction involves only
finitely many degrees and finitely many choices in each degree. For modules use the module
free-resolution clause and the exact forgetful functor of
`lem-weil-pbc-module-sheaves-colimits-forgetful`; local lifts are supplied by
`lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective`. The same corrections establish the
module-category comparison and its colimit universal property. -/
theorem hypercover_cohomology (X : Scheme.{u₁}) [CompactSpace X] [QuasiSeparatedSpace X]
    (q : ℕ) :
    FiniteSplitEtaleHypercover.IsCohomologyColimit AddCommGrpCat.{u₁ + 1} q
      (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u₁ + 1}) 0 ⋙
        Etale.cohomology AddCommGrpCat.{u₁ + 1} X (q : ℤ)) ∧
    ∀ (R : Type (u₁ + 1)) [Ring R],
      FiniteSplitEtaleHypercover.IsCohomologyColimit (ModuleCat.{u₁ + 1} R) q
        (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology (ModuleCat.{u₁ + 1} R)) 0 ⋙
          Etale.cohomology (ModuleCat.{u₁ + 1} R) X (q : ℤ)) := by
  sorry

end AlgebraicGeometry
