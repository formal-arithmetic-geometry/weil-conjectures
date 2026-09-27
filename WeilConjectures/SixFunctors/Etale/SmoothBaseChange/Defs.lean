/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper

/-!
# The recorded base-change property and the allowed coefficients

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Blueprint `sk-def-smooth`: Smooth and allowed coefficients -/
def Scheme.IsAllowedTorsionSheaf (S : Scheme.{u}) {T : Scheme.{u}}
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ T)
    (x : ↥((pointSmallEtale s).sheafFiber.obj F)),
    ∃ n : ℕ, 0 < n ∧ IsUnit (n : Γ(S, ⊤)) ∧ n • x = 0

variable {X S : Scheme.{u}}

/-- Blueprint `sk-def-bc`: The recorded base-change property -/
def Etale.BaseChangeProperty (p : X ⟶ S) (q : ℤ) : Prop :=
  ∀ {T Y : Scheme.{u}} (g : T ⟶ S) (e : Y ⟶ T) (h : Y ⟶ X)
    [QuasiCompact g] [QuasiSeparated g] (sq : IsPullback e h g p)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
    IsIso ((DerivedCategory.Plus.homologyFunctor _ q).map
      ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))

end AlgebraicGeometry
