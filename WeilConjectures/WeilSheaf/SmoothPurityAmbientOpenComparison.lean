/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityAmbientPullbackCoordinates
public import WeilConjectures.WeilSheaf.SmoothPurityAmbientOpenExchange
public import WeilConjectures.WeilSheaf.SmoothPurityOpenExchangeCoordinates

/-! # The specified open exchange in the scheme-indexed formalism -/

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
  {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
  {f' : X' ⟶ Y'} {g' : X' ⟶ X}
  [IsOpenImmersion g] [IsOpenImmersion g']

/-- The formal open mate is the specified exact-derived exchange in total-pullback coordinates. -/
lemma purityAmbientOpenBaseChange_eq (sq : IsPullback g' f' f g)
    [WeaklyEtale f] [WeaklyEtale f'] :
    ((purityAmbientExchangeFormalism Λ).baseChange f' g' g f sq.w.symm).natTrans =
      Functor.whiskerRight (leftDerivedUpperStarIsoMapDerivedCategory Λ f').hom
        D((g')_!open⟦Λ⟧) ≫
      (openImmersionLowerShriekMapDerivedCategoryBaseChangeIso Λ sq).inv ≫
      Functor.whiskerLeft D((g)_!open⟦Λ⟧)
        (leftDerivedUpperStarIsoMapDerivedCategory Λ f).inv := by
  have hc := Adjunction.purity_exchangeLeft_coordinates
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ g)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ g')
    (leftDerivedUpperStarIsoMapDerivedCategory Λ g).symm
    (leftDerivedUpperStarIsoMapDerivedCategory Λ g').symm
    (leftDerivedUpperStarIsoMapDerivedCategory Λ f')
    (leftDerivedUpperStarIsoMapDerivedCategory Λ f)
    (pullbackSquareComparison Λ sq.toCommSq)
    (Functor.mapDerivedCategorySquareIso (upperStarSquareComparison Λ sq.toCommSq))
    (purityAmbientPullbackSquareComparison_coordinates Λ sq.toCommSq)
  rw [← purityOpenImmersionLowerShriekMapDerivedCategoryBaseChangeIso_inv Λ sq] at hc
  rw [purityAmbientPullbackSquareComparison_eq_sqIso] at hc
  simpa only [Adjunction.exchangeLeft_eq_mateEquiv_symm,
    purityAmbientExchangeFormalism, ExchangeFormalism.baseChange] using hc

end AlgebraicGeometry.ProEtale.CondensedRing
