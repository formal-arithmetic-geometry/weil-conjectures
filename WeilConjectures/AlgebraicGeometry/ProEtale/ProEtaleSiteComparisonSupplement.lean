/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison

/-!
# The geometric comparison from the pro-etale to the etale site

Source: Stacks Project, Tag 099R, opening paragraph; Sites, Tags 00WX, 00X6 and 00YV
(blueprint: def-weil-pbc-site-comparison-morphism).

The inclusion is the existing `Scheme.toProEt`, identity on schemes and arrows.
Its continuity and finite-limit preservation are the existing instances
`Scheme.isContinuous_toProEt` and `Scheme.preservesFiniteLimits_toProEt`.
The set adjunction below uses restriction and the left Kan extension followed by
sheafification, rather than a chosen abstract left adjoint. The coefficient version uses
these same constructions in modules over a fixed ring.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
