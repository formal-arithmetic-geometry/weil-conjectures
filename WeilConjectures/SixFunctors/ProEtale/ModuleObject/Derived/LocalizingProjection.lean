/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionMapShift

/-!
# The projection formula on the localizing categories `Loc(Dbc)`

Let `Λ` be a commutative condensed ring and `p : X ⟶ Y` a morphism of schemes. This file proves
the formal part of the projection formula on the localizing categories (blueprint
`det-thm-sf-pf-field-localizing`, `det-thm-sf-pf-adic-projection` (2)): if

* the projection map `Rp_*M ⊗ᴸ L ⟶ Rp_*(M ⊗ᴸ Lp^*L)` is an isomorphism for `M` in `Dbc(X, Λ)` and
  `L` in `Dbc(Y, Λ)`,
* `Rp_*` maps `Loc(Dbc(X, Λ))` into `Loc(Dbc(Y, Λ))` and preserves direct sums there,
* `Lp^*` maps `Dbc(Y, Λ)` into `Dbc(X, Λ)`, and `Dbc(X, Λ)` is closed under `⊗ᴸ`,

then the projection map is an isomorphism for `M` in `Loc(Dbc(X, Λ))` and `L` in
`Loc(Dbc(Y, Λ))`. Both sides are exact functors of each variable preserving direct sums, and the
projection map is compatible with the shifts in each variable
(`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionMapShift`), so this is the
two-variable determination argument
`CategoryTheory.NatTrans.isIso_app_app_of_localizingClosure` (blueprint
`sk-lem-sf-determination`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

set_option hygiene false in
/-- The derived category `D(X_proét, Λ) = D(Mod_{Λ_X})` of module objects over `Λ_X`. -/
local notation "𝔻(" X ")" =>
  DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (p : X ⟶ Y)

end AlgebraicGeometry.ProEtale.CondensedRing
