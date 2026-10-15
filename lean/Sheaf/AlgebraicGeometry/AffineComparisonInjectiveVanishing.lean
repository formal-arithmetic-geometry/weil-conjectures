/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.AlgebraicGeometry.EtaleCohomologyLimitOfSchemes
import WeilConjectures.CategoryTheory.SiteCechComplex
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import Sheaf.RingTheory.IndEtaleStability
import Sheaf.CategoryTheory.SiteCechVanishingCriterion
import Sheaf.RingTheory.IndPrincipalZariski
import Sheaf.CategoryTheory.ExistsDirectedReindexing
import Sheaf.AlgebraicGeometry.FibreProductLimit
import Sheaf.AlgebraicGeometry.LimitAffineTransition
import Sheaf.AlgebraicGeometry.AffineEtaleSiteColimit
import Mathlib.AlgebraicGeometry.Sites.Etale
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Sheaf.CategoryTheory.InjectiveSheafCechAcyclic

/-!
# Affine vanishing for comparison pullbacks of injective abelian sheaves

Source: Stacks Project, Pro-etale Cohomology, Tag 099U, `lemma-affine-vanishing`
(blueprint: lem-cbc-abelian-affine-comparison-vanishing).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- On an affine scheme, the comparison inverse image of any injective abelian etale
sheaf has zero positive pro-etale cohomology. No restriction on coefficients is imposed.
Source: Stacks Project, Tag 099U, `lemma-affine-vanishing`
(blueprint: lem-cbc-abelian-affine-comparison-vanishing).

Proof:
1. The comparison section formula (lem-cbc-comparison-pullback-sections) identifies
   sections of F = nu⁻¹J with etale sections of the inverse image of J. Naturality for
   addition, zero and negation makes this an identification of abelian groups, compatible
   with all restriction maps. On etale objects it identifies F with J.
2. Degree-zero continuity (lem-weil-pbc-etale-cohomology-limit-of-schemes) identifies
   sections on an affine directed limit with the colimit of sections at its stages.
   All affine objects are qcqs (lem-weil-pbc-affine-scheme-qcqs).
3. Exact filtered colimits of abelian groups commute with finite products, kernels,
   images and cohomology. Applied degreewise to the site Cech complex, the section
   comparisons commute with every omitted-factor restriction and hence the differential.
4. The affine ind-etale basis and ind-etale stability provide finite cofinal covers
   closed under intersections, verifying the first two hypotheses of the site Cech
   vanishing criterion (lem-weil-pbc-site-cech-vanishing-criterion).
5. Present each member of such a finite cover as a directed limit of affine etale
   objects. Replace the finitely many indices by their product using directed cofinal
   reindexing. Each stage family is surjective, since the limit family is. Fibre products
   commute with limits (lem-kun-fibre-product-limits); the affine limits exist by
   lem-weil-pbc-limit-affine-transition. The empty cover has zero Cech complex.
6. Steps 2 and 3 reduce positive Cech vanishing to finite affine etale covers of a
   basis object, without asserting injectivity on a different etale site.
7. Present that basis object as a directed limit of affine etale Y-schemes. Descend the
   finite cover by lem-weil-pbc-affine-etale-site-colimit; descend its target isomorphism
   and inverse to fix the target at a common later stage. Etale composition, cancellation
   and base change put all stage intersections on the original etale site. The tail is
   cofinal, and its intersections have the required affine limits.
8. Apply steps 2 and 3 again, including naturality for face maps. At each stage step 1
   identifies the entire Cech complex with that for J on Y_et. Injectivity of J on this
   fixed site gives positive Cech vanishing by lem-weil-pbc-injective-sheaf-cech-acyclic.
9. The site Cech criterion now gives positive cohomology vanishing on every basis
   object. The identity of affine Y is ind-etale and belongs to the basis; take it as
   the object. This includes empty Y, for which the empty-cover complex is zero.

Mathlib's H is the Ext encoding of right derived global sections. Its result is a type,
so vanishing is expressed by Subsingleton. HasExt.standard fixes a model without an
additional hypothesis. Natural degrees q > 0 are exactly the positive integer degrees.
-/
theorem subsingleton_cohomology_comparisonUpperStar_obj_of_injective_of_isAffine
    (Y : Scheme.{u}) [IsAffine Y]
    (J : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) [Injective J]
    (q : ℕ) (hq : 0 < q) :
    Subsingleton (@Sheaf.H _ _ _
      ((comparisonUpperStar AddCommGrpCat.{u + 1} Y).obj J) _ (HasExt.standard _) q) := by
  sorry

end AlgebraicGeometry.ProEtale
