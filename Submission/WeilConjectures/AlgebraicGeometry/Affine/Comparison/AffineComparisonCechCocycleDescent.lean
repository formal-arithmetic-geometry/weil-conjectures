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
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech

import Submission.WeilConjectures.AlgebraicGeometry.Affine.Comparison.AffineComparisonEtaleCechPresentation
import Submission.WeilConjectures.AlgebraicGeometry.AffineEtaleCechSystem.AffineComparisonCechSystemSections
import Submission.WeilConjectures.CategoryTheory.Sites.ProperBaseChange.OrderedCechUliftComparison

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Descent of finite affine comparison Čech cocycles

Source: Stacks Project, Tag 099U, the two finite Čech limit reductions in condition (3).
(blueprint: lem-cbc-affine-comparison-cech-cocycle-descent).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

end AlgebraicGeometry.ProEtale
