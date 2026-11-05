/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ExchangeConjugate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.WeaklyEtale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.WeaklyEtaleProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SquareComparisonCoherence

/-! # Base change for the exact weakly étale left adjoint

Conjugating weakly étale direct-image base change gives base change for the
left adjoint to weakly étale pullback, on the entire ambient derived category.
The transverse morphism is arbitrary.
-/

set_option profiler true
set_option profiler.threshold 0

@[expose] public noncomputable section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  {X Y X' Y' : Scheme.{u}} {h : X ⟶ Y} {h' : X' ⟶ Y'}
  {πX : X' ⟶ X} {πY : Y' ⟶ Y} [WeaklyEtale h] [WeaklyEtale h']

/-- The inverse mate for the exact weakly étale lower shriek is invertible
under arbitrary cartesian base change. -/
theorem purity_isIso_weaklyEtaleAmbientExchange (sq : IsPullback πX h' h πY) :
    IsIso (Adjunction.exchangeLeft
      (derivedWeaklyEtaleLowerShriekLeftDerivedUpperStarAdjunction Λ h)
      (derivedWeaklyEtaleLowerShriekLeftDerivedUpperStarAdjunction Λ h')
      (pullbackSquareComparison Λ sq.toCommSq.flip)) := by
  apply (Adjunction.isIso_exchangeRight_iff_isIso_exchangeLeft
    (derivedUpperStarLowerStarAdjunction Λ πY)
    (derivedUpperStarLowerStarAdjunction Λ πX) _ _ _).mp
  exact isIso_baseChangeMap_of_weaklyEtale Λ sq.flip

end AlgebraicGeometry.ProEtale.CondensedRing
