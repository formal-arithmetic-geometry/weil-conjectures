/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.SmoothPurity.SeparablyClosedTorsionCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.SixFunctors.EllCohomologicalDimensionComparison
import WeilConjectures.AlgebraicGeometry.Base.BaseFieldFiniteTorsionCohomologicalDimension

/-!
# Cohomological dimension of the base field

Source: blueprint `sec-six-functors-basics/sk-lem-base-field-cd`, order 1507;
Stacks Project, Tags 03QQ and 010T (blueprint: sk-lem-base-field-cd).
The dimension and its local prime-power torsion convention are those of `sk-def-cd`.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry.ProEtale

open CategoryTheory

end AlgebraicGeometry.ProEtale
