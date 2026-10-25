/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.CurveLocal.ExchangeRestriction

/-!

# Exceptional pullback along a closed immersion on the strict localization

Let `M` be a strictly local model of a curve (`AlgebraicGeometry.Etale.CurveLocalModel`) and
`ι ≫ graph = d ≫ diagonal` a cartesian square with fixed scheme `F`, so that `d : F ⟶ X` is a
closed immersion and `Y = F ×_X B` (`AlgebraicGeometry.Etale.CurveLocalModel.isPullback_τY`),
where `B ⟶ X` is the strict localization of `X` at the fixed point `y`. This file proves that
the base change map `Lτ_Y^* Rd^! N ⟶ Ry_B^! Lτ_B^* N` of the exceptional pullback
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekBaseChangeMap`) becomes an isomorphism after
derived global sections over `Y`, for bounded below `N`: the stalk of `Rd^! N` at `y` is the
local cohomology `RΓ_Y(B, N|_B)` on the strict localization.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.CurveLocalModel

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k] [IsAlgClosed k]
  (M : CurveLocalModel k) {F : Scheme.{u}} {ι d : F ⟶ M.X} [IsClosedImmersion d]
  (hsq : IsPullback ι d M.graph (pullback.diagonal M.f))

/-- **Stalks of the exceptional pullback on the strict localization**: for bounded below `N`, the
base change map `Lτ_Y^* Rd^! N ⟶ Ry_B^! Lτ_B^* N` induces an isomorphism on derived global
sections over `Y = F ×_X B`. -/
theorem isIso_rightDerivedGlobalSections_map_rightDerivedUpperShriekBaseChangeMap
    (N : DerivedCategory.Plus (Sheaf M.X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) M.Y).map
      ((rightDerivedUpperShriekBaseChangeMap Λ (M.isPullback_τY hsq)).app N.obj)) :=
  sorry

end AlgebraicGeometry.Etale.CurveLocalModel
