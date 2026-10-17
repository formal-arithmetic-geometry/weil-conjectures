/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.OpenImmersion.Defs

/-!
# Base change along open immersions at non-closed points

This file contains the two "stalks over points with positive transcendence degree" steps of the
proof of blueprint `lem-kun-0f1h`: if the statement holds for all data with smaller
`dim X + dim Y`, then the base change map is an isomorphism on the geometric stalk at every
point `z ∈ X ×_K Y` whose image in `X` (resp. in `Y`) is not closed. The proof base changes the
square to the strict henselization `X' = Spec O^{sh}_{X,x}` (resp. `Y' = Spec O^{sh}_{Y,y}`),
a limit of étale `X`-schemes (smooth base change in the limit form, blueprint `lem-kun-0f09`),
writes it as a limit of affine schemes of finite type and smaller dimension over a separably
closed field `L` (blueprint `lem-kun-0f0u`), and passes to the limit (blueprint
`lem-kun-0ezt`, with `lem-kun-descent-limit-open` for the open `U`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Proof of blueprint `lem-kun-0f1h`, stalks at points `z` whose image `x` in `X` is not closed
(so that `trdeg_K κ(x) > 0`): if `lem-kun-0f1h` holds for all data with smaller `dim X + dim Y`,
the base change map is an isomorphism on the geometric stalk at `z`. -/
theorem Etale.isIso_sheafFiber_baseChangeHomologyMap_of_not_isClosed_fst {K : Type u} [Field K]
    {X U Y W V : Scheme.{u}} (aX : X ⟶ Spec (.of K)) (aY : Y ⟶ Spec (.of K))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (j : U ⟶ X) [IsOpenImmersion j] (q₁ : W ⟶ X) (q₂ : W ⟶ Y) (hW : IsPullback q₁ q₂ aX aY)
    (e : V ⟶ U) (h : V ⟶ W) (sq : IsPullback e h j q₁) (n : ℕ) (hn : IsUnit (n : K))
    (hΛ : (n : Λ) = 0)
    (IH : Etale.OpenImmersionBaseChangeBelow Λ (topologicalKrullDim X + topologicalKrullDim Y))
    (z : W) (hz : ¬ IsClosed ({q₁.base z} : Set X)) (i : ℤ)
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso ((W.uliftPointSmallEtale z).sheafFiber.map (Etale.baseChangeHomologyMap Λ sq i F)) :=
  sorry

/-- Proof of blueprint `lem-kun-0f1h`, stalks at points `z` whose image `y` in `Y` is not closed
(so that `trdeg_K κ(y) > 0`): if `lem-kun-0f1h` holds for all data with smaller `dim X + dim Y`,
the base change map is an isomorphism on the geometric stalk at `z`. This step also uses the
base change along the field extension `K ⊆ L` (blueprint `lem-kun-0f1c`). -/
theorem Etale.isIso_sheafFiber_baseChangeHomologyMap_of_not_isClosed_snd {K : Type u} [Field K]
    {X U Y W V : Scheme.{u}} (aX : X ⟶ Spec (.of K)) (aY : Y ⟶ Spec (.of K))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (j : U ⟶ X) [IsOpenImmersion j] (q₁ : W ⟶ X) (q₂ : W ⟶ Y) (hW : IsPullback q₁ q₂ aX aY)
    (e : V ⟶ U) (h : V ⟶ W) (sq : IsPullback e h j q₁) (n : ℕ) (hn : IsUnit (n : K))
    (hΛ : (n : Λ) = 0)
    (IH : Etale.OpenImmersionBaseChangeBelow Λ (topologicalKrullDim X + topologicalKrullDim Y))
    (z : W) (hz : ¬ IsClosed ({q₂.base z} : Set Y)) (i : ℤ)
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso ((W.uliftPointSmallEtale z).sheafFiber.map (Etale.baseChangeHomologyMap Λ sq i F)) :=
  sorry

variable {Λ} in
/-- Proof of blueprint `lem-kun-0f1h`, stalks at non-closed points: a point of `X ×_K Y` is
closed if and only if both of its images are closed (blueprint `lem-kun-closed-points-of-product`),
so the two previous steps give the isomorphism on the geometric stalks at all non-closed points,
as soon as `lem-kun-0f1h` holds for all data with smaller `dim X + dim Y`. -/
theorem Etale.openImmersionBaseChangeAtNonClosed_of_below {N : WithBot ℕ∞}
    (H : Etale.OpenImmersionBaseChangeBelow Λ N) : Etale.OpenImmersionBaseChangeAtNonClosed Λ N :=
  sorry

end AlgebraicGeometry
