/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimensionSupplement

import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful
import WeilConjectures.AlgebraicGeometry.Sites.EtaleTorsion
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Algebra.Category.Grp.Zero

/-!
# Pro-étale and étale primary cohomological dimensions agree

Source: current blueprint, `sec-six-functors-basics/sk-def-cd/`
`sk-def-cd-etale-comparison.md`, clauses 1--4 (blueprint: det-cd-etale-comparison).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

end AlgebraicGeometry.ProEtale
