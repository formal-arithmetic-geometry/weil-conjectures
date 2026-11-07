/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
public import Submission.WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import Submission.WeilConjectures.CategoryTheory.Sites.CechComplex
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products

import Submission.WeilConjectures.AlgebraicGeometry.Affine.Comparison.AffineComparisonCechCocycleDescent
import Submission.WeilConjectures.CategoryTheory.InjectiveSheafCechAcyclic
import Submission.WeilConjectures.AlgebraicGeometry.EtaleCohomologyLimitOfSchemes
import Submission.WeilConjectures.RingTheory.ProperBaseChange.IndEtaleStability
import Submission.WeilConjectures.CategoryTheory.ExistsDirectedReindexing
import Mathlib.AlgebraicGeometry.Pullbacks
import Submission.WeilConjectures.AlgebraicGeometry.LimitAffineTransition
import Submission.WeilConjectures.AlgebraicGeometry.FullAffineEtaleSite
import Mathlib.CategoryTheory.Sites.Continuous
import Submission.WeilConjectures.CategoryTheory.FinitePrecoverage
import Submission.WeilConjectures.CategoryTheory.ArrowsFunctor
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.ProEtaleComparisonPullbackSections
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import Submission.WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Submission.WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import Submission.WeilConjectures.CategoryTheory.SiteCechComplex
import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Finite affine Čech exactness for comparison pullbacks of injectives

Source: Stacks Project, Tag 099U, verification of condition (3).
(blueprint: lem-cbc-abelian-affine-comparison-vanishing-aux).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

end AlgebraicGeometry.ProEtale
