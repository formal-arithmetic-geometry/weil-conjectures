/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProperBaseChange.IntegralFinitePullbackComposition
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence

/-! # The canonical pullback compositor in the internal condensed-module presentation

Source: Stacks, Tags 0D6D and 03D3, and the blueprint module-derived convention.
(blueprint: lem-weil-pbc-proetale-derived-pullback-composition)

The arbitrary ring-sheaf comparison remains publicly imported. This exposes the same
termwise tensor comparison for the internal module-object encoding used by transport.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The native canonical compositor: on K-flat representatives it is the localization
of the termwise tensor pullback comparison, with its actual coefficient identifications.
This is an alias of the published comparison, with no new choice or hypothesis.
Source: Stacks, Tags 0D6D and 03D3.
(blueprint: lem-weil-pbc-proetale-derived-pullback-composition) -/
abbrev condensedCanonicalPullbackComposition
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Z W V : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) :=
  leftDerivedUpperStarComp Λ h k

end AlgebraicGeometry.ProEtale.CondensedRing
