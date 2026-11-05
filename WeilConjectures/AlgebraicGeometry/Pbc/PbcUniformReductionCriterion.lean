/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcUniformReductionProfile
import WeilConjectures.AlgebraicGeometry.Pbc.PbcUniformLocalModelCohomology

import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonDerived
import WeilConjectures.AlgebraicGeometry.Normalized.NormalizedConstructibleTowerLocalEffectivity
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.LevelwiseAdicTruncations

/-! # A uniform cohomology criterion for compatible constructible reductions
Source: the uniform triangulation node, steps 2, 6 and 7.
(blueprint: lem-weil-pbc-uniform-reduction-criterion). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme
open ProEtale

end AlgebraicGeometry.Scheme
