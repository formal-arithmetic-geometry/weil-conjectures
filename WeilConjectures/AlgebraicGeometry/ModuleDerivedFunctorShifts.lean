/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ModuleDerivedFunctorCompositorShifts

/-!
# Specified integer shifts on derived module pullback and pushforward

Source: Stacks Project, derived.tex, Tags 014X, 015F and 05SE;
blueprint compactification coherence, refinement (2)
(blueprint: def-sfb-module-derived-functor-shifts).

The three constructions of this node are the published declarations of
`WeilConjectures.AlgebraicGeometry.ModuleDerivedFunctorCompositorShifts`, reexported here unchanged:
`modulePullbackExactComparison` (the canonical universal-counit comparison
`c_u : Lu^* ≅ D(u^*)`), `modulePullbackDerivedCommShift` (the termwise shifts of `D(u^*)`
transported along `c_u`, by `Functor.CommShift.ofIso`) and
`modulePushforwardDerivedCommShift` (the published K-injective shifts on `Ru_*`).
They are not redeclared, so that one definition per notion is kept.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The canonical exact comparison `c_f : Lf^* ≅ D(f^*)` of the specified K-flat module
pullback, the transparent name of the published `modulePullbackExactComparison`
(`leftDerivedExactComparison` with the universal counit). The shift structures of this node
are `modulePullbackDerivedCommShift`, transported along it, and
`modulePushforwardDerivedCommShift`.
Source: Stacks Tags 014X, 015F and 05SE
(blueprint: def-sfb-module-derived-functor-shifts). -/
abbrev modulePullbackCanonicalExactComparison :
    (moduleObjectDerivedPullback Λ f) ≅ (upperStar Λ f).mapDerivedCategory :=
  modulePullbackExactComparison Λ f

end AlgebraicGeometry.ProEtale.CondensedRing
