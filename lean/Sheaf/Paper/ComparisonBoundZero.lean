/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import Sheaf.CategoryTheory.SiteCoveringAxioms
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import Sheaf.AlgebraicGeometry.ProEtaleComparisonPullbackSections
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Sheaf.CategoryTheory.RingedSiteGrothendieckAbelian
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Sheaf.CategoryTheory.ModuleAbelianEvaluationComparison
import Sheaf.Paper.SiteHigherDirectImageSheafifiedPresheaf
import Sheaf.CategoryTheory.SitePullbackAbelianExact
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian

/-!
# The comparison bound for sheaves of étale origin

Source: blueprint, `sec-smooth-purity/sk-prop-sf-fullcd-etale-origin/`
`prop-sf-comparison-bound-zero.md`, statement and proof
(blueprint: prop-sf-comparison-bound-zero); Stacks Project, Tags 099T and 099V.

We use the fixed-coefficient module-valued sheaves and the canonical adjunction
recorded by `Scheme.proEtaleSiteComparisonModules`. The positive right derived
functors are Mathlib's functors computed by injective module resolutions.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- The comparison unit is invertible on every étale module sheaf, and the comparison
right derived functors vanish in every positive degree on its pullback and on every
sheaf of étale origin. No constructibility or finiteness condition is imposed on the
sheaf, and the scheme is arbitrary. In particular this covers every coefficient sheaf
in `def-sf-fullcd-used-class`, with the finite coefficient rings of
`def-weil-l-adic-coefficient-extension`.
Source: blueprint `prop-sf-comparison-bound-zero`, statement and proof steps 1--5;
Stacks Project, Tags 099T, 099V, 03FD, 072W and 015E
(blueprint: prop-sf-comparison-bound-zero).

Proof:
1. By `lem-cbc-comparison-pullback-sections`, the comparison unit on sets is bijective
at every étale object. Inverse image carries addition and every scalar endomorphism
along with the underlying sheaf. Naturality makes the unit and its inverse linear
and compatible with restrictions. Local constant representatives from
`lem-weil-pbc-site-sheafification-sections-local` and
`lem-pc-sites-sheafification-underlying-sets` identify this fixed-scalar structure
with modules over the constant ring sheaf. The lifted adjunction's unit is precisely
this unit, giving the first clause.
2. Resolve any abelian étale sheaf B by injectives. Exactness from
`lem-weil-pbc-site-pullback-abelian-exact` makes its inverse image an exact resolution.
The inverse images of the injectives are comparison-acyclic by
`lem-cbc-abelian-comparison-injective-acyclicity`. Compute direct images by this
acyclic resolution using `lemma-weil-pbc-leray-acyclicity`. The natural units identify
the pushed-forward complex with the original resolution, giving abelian vanishing.
3. Module sheaf categories have enough injectives by
`lem-pur-ringed-site-grothendieck-abelian` and `lem-sp-grothendieck-enough-injectives`.
Their forgetful functors are exact and faithful by
`lem-weil-pbc-module-sheaves-colimits-forgetful`. For an injective module sheaf J,
`lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison` gives vanishing of
positive abelian cohomology at each site object. Thus
`lem-weil-pbc-site-higher-direct-image-sheafified-presheaf` makes its underlying
abelian sheaf comparison-acyclic; it need not be injective as an abelian sheaf.
4. Forget an injective module resolution of M. Step 3 makes it an acyclic abelian
resolution, and restriction commutes with forgetting scalars. Exactness of the
étale forgetful functor identifies the underlying abelian sheaf of each module
right derived image with the corresponding abelian right derived image. For M the
inverse image of G, step 2 makes these zero in positive degrees. Faithfulness of
forgetting scalars then gives the second clause.
5. Apply each right derived functor to the isomorphism witnessing membership in the
essential image and transport the vanishing, giving the final clause. For the source's
finite-field application, the coefficient quotient at n ≥ 1 is a finite commutative
ring by `Padic.finite_coefficientExtensionRing`; its étale-origin witness is exactly
the essential-image hypothesis. No property of the base field or dimension enters. -/
theorem comparison_bound_zero (X : Scheme.{u}) (A : Type (u + 1))
    [CommRing A] [Finite A] :
    (∀ G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A),
      IsIso ((X.proEtaleSiteComparisonModules A).unit.app G) ∧
        ∀ q : ℕ, 0 < q →
          IsZero (((comparisonLowerStar (ModuleCat.{u + 1} A) X).rightDerived q).obj
            ((comparisonUpperStar (ModuleCat.{u + 1} A) X).obj G))) ∧
    (∀ F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A),
      (comparisonUpperStar (ModuleCat.{u + 1} A) X).essImage F →
        ∀ q : ℕ, 0 < q →
          IsZero (((comparisonLowerStar (ModuleCat.{u + 1} A) X).rightDerived q).obj F)) := by
  sorry

end AlgebraicGeometry.ProEtale
