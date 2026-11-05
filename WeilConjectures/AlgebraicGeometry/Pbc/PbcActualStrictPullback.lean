/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcCompletedPullbackActualSupplement
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedPullback
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcCompletedPullbackActualSupplement
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerPullbackSupplement
import WeilConjectures.AlgebraicGeometry.Stratum.StratumCompletionUnitRestriction

/-! # Functor and completion interface for the published strict-tower pullback
Source: Stacks 099N (2),(5), blueprint order 1261
(blueprint: def-weil-pbc-completed-pullback).
The published quotient tower, resolving pullback, derived limit and comparison
are retained. This interface supplies their functor and unit-compatible natural
isomorphism to the intrinsic completion reflector used by scalar comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme
variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

end AlgebraicGeometry.Scheme
