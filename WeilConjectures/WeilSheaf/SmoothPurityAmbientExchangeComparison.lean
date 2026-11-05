/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityAmbientExchangeFormalism
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing

/-! # The ambient proper exchange in the scheme-indexed formalism -/

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

/-- The existing derived square comparison is the square in the ambient formalism. -/
lemma purityAmbientPullbackSquareComparison_eq_sqIso (sq : CommSq g' f' f g) :
    pullbackSquareComparison Λ sq =
      (purityAmbientExchangeFormalism Λ).sqIso f' g' g f sq.w.symm := by
  rw [ExchangeFormalism.sqIso, ExchangeFormalism.pbComp'_rfl]
  unfold ExchangeFormalism.pbComp' pullbackSquareComparison
  rfl

/-- The actual derived direct-image exchange is the formal proper exchange. -/
lemma purityAmbientBaseChangeMap_eq_pfBaseChange (sq : CommSq g' f' f g) :
    baseChangeMap Λ sq =
      ((purityAmbientExchangeFormalism Λ).pfBaseChange g' f' f g sq.w).natTrans := by
  rw [baseChangeMap, Adjunction.exchangeRight_eq_mateEquiv,
    ExchangeFormalism.pfBaseChange, purityAmbientPullbackSquareComparison_eq_sqIso,
    ← Iso.symm_hom, ExchangeFormalism.sqIso_symm]
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing
