/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.OpenImmersion.Defs

/-!
# Base change along open immersions: the projective case

This file contains the "projective case" of the proof of blueprint `lem-kun-0f1h`: if `Y` is
proper (e.g. projective) over `K` and the base change map is an isomorphism on the geometric
stalks at all non-closed points of `X ×_K Y`, then it is an isomorphism. After the reduction to a
separably closed ground field (blueprint `lem-kun-0f1h-sep-reduction`), the cone `Q` of the
derived base change map is supported on closed points, so it vanishes as soon as its cohomology
does (blueprint `lem-kun-0f1g`), and the base change map induces an isomorphism on cohomology by
the Künneth formula with one proper factor (blueprint `lem-kun-bc-kunneth-compat`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Proof of blueprint `lem-kun-0f1h`, the projective case: for `Y` proper over `K`, if the
base change map at `F` is an isomorphism on the geometric stalks at all non-closed points of
`W = X ×_K Y`, then it is an isomorphism. -/
theorem Etale.isIso_baseChangeHomologyMap_of_isProper_of_forall_not_isClosed {K : Type u}
    [Field K] {X U Y W V : Scheme.{u}} (aX : X ⟶ Spec (.of K)) (aY : Y ⟶ Spec (.of K))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [IsProper aY]
    (j : U ⟶ X) [IsOpenImmersion j] (q₁ : W ⟶ X) (q₂ : W ⟶ Y) (hW : IsPullback q₁ q₂ aX aY)
    (e : V ⟶ U) (h : V ⟶ W) (sq : IsPullback e h j q₁) (n : ℕ) (hn : IsUnit (n : K))
    (hΛ : (n : Λ) = 0) (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : ∀ z : W, ¬ IsClosed ({z} : Set W) → ∀ i : ℤ,
      IsIso ((W.uliftPointSmallEtale z).sheafFiber.map (Etale.baseChangeHomologyMap Λ sq i F)))
    (i : ℤ) : IsIso (Etale.baseChangeHomologyMap Λ sq i F) :=
  sorry

end AlgebraicGeometry
