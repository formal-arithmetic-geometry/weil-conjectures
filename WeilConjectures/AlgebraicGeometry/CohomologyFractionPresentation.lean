/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.OpenModuleCohomology
public import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # Degree-zero fractions of twisted module cohomology

Source: Stacks Project, Cohomology of Schemes, Lemma 09MR, equation preceding the lemma
(blueprint: def-sc-cohomology-fraction-presentation).

The underlying additive group of the degree-zero homogeneous localization has the
presentation with generators `[n, ξ]` and relations `[n, ξ] = [n+b, s^b ξ]`.
Only nonnegative numerator degrees enter degree-zero fractions, even though the full
cohomology module is graded by integers. The quotient retains all torsion relations.
-/

@[expose] public section

universe uCF

open CategoryTheory MonoidalCategory DirectSum

namespace AlgebraicGeometry.Scheme.Modules

end AlgebraicGeometry.Scheme.Modules
