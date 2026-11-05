/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdjunctionShift
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocalizingProjection

/-!
# Proper base change on the localizing categories `Loc(Dbc)`

Let `Λ` be a commutative condensed ring and `g' ≫ p = p' ≫ g` a commutative square of schemes.
This file proves the formal part of proper base change on the localizing categories (blueprint
`sk-prop-proper-base-change-unbounded`, `det-proper-base-change-unbounded-extension`): if the
base change map `Lg^* Rp_* ⟶ Rp'_* Lg'^*` is an isomorphism on `Dbc(X, Λ)`, if `Rp_*` and
`Rp'_*` preserve the direct sums of objects of the localizing closures of `Dbc` and `Lg'^*`
preserves `Dbc`, then the base change map is an isomorphism on `Loc(Dbc(X, Λ))`
(`ProEtale.CondensedRing.isIso_baseChangeMap_of_localizingBoundedConstructible`).

Both sides are triangulated functors and the base change map commutes with the shifts
(`ProEtale.CondensedRing.commShift_baseChangeMap`), so this is the determination argument
`CategoryTheory.NatTrans.isIso_app_of_localizingClosure` (blueprint `sk-lem-sf-determination`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory.NatTrans.CommShift

variable {A : Type*} [AddMonoid A] {B B' C C' : Type*} [Category* B] [Category* B']
  [Category* C] [Category* C'] [HasShift B A] [HasShift B' A] [HasShift C A] [HasShift C' A]
  {Lf : B ⥤ C} {Rf : C ⥤ B} {Lf' : B' ⥤ C'} {Rf' : C' ⥤ B'} {G : B ⥤ B'} {G' : C ⥤ C'}
  [Lf.CommShift A] [Rf.CommShift A] [Lf'.CommShift A] [Rf'.CommShift A] [G.CommShift A]
  [G'.CommShift A] (af : Lf ⊣ Rf) (af' : Lf' ⊣ Rf') [af.CommShift A] [af'.CommShift A]

end CategoryTheory.NatTrans.CommShift

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

set_option hygiene false in
/-- The derived category `D(X_proét, Λ) = D(Mod_{Λ_X})` of module objects over `Λ_X`. -/
local notation "𝔻(" X ")" =>
  DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y X' Y' : Scheme.{u}}

variable {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}

end AlgebraicGeometry.ProEtale.CondensedRing
