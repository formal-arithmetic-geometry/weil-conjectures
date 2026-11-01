/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdjunctionShift
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocalizingProjection
public import WeilConjectures.TraceFormula.Specialization.GenericDivisorShift

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

/-- The exchange morphism `Rf ⋙ G ⟶ G' ⋙ Rf'` of adjunctions commuting with the shifts, along an
isomorphism `G ⋙ Lf' ≅ Lf ⋙ G'` commuting with the shifts, commutes with the shifts. -/
instance exchangeRight (θ : G ⋙ Lf' ≅ Lf ⋙ G') [NatTrans.CommShift θ.hom A] :
    NatTrans.CommShift (Adjunction.exchangeRight af af' θ) A := by
  dsimp only [Adjunction.exchangeRight, Functor.squareTransport]
  infer_instance

end CategoryTheory.NatTrans.CommShift

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

set_option hygiene false in
/-- The derived category `D(X_proét, Λ) = D(Mod_{Λ_X})` of module objects over `Λ_X`. -/
local notation "𝔻(" X ")" =>
  DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y X' Y' : Scheme.{u}} {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The base change map `Lg^* Rp_* ⟶ Rp'_* Lg'^*` of a commutative square commutes with the
shifts. -/
instance commShift_baseChangeMap (sq : CommSq g' p' p g) :
    NatTrans.CommShift (baseChangeMap Λ sq) ℤ :=
  NatTrans.CommShift.exchangeRight (derivedUpperStarLowerStarAdjunction Λ p)
    (derivedUpperStarLowerStarAdjunction Λ p') (pullbackSquareComparison Λ sq)

/-- The formal part of blueprint `sk-prop-proper-base-change-unbounded` and
`det-proper-base-change-unbounded-extension`, for an arbitrary condensed ring `Λ`: proper base
change extends from `Dbc` to `Loc(Dbc)`.

Let `g' ≫ p = p' ≫ g` be a commutative square. Assume that `Rp_*` and `Rp'_*` preserve the
direct sums of objects of `Loc(Dbc(X, Λ))`, resp. `Loc(Dbc(X', Λ))`, that `Lg'^*` maps
`Dbc(X, Λ)` into `Dbc(X', Λ)` and that the base change map `Lg^* Rp_*K ⟶ Rp'_* Lg'^*K` is an
isomorphism for `K` in `Dbc(X, Λ)`. Then it is an isomorphism for `K` in `Loc(Dbc(X, Λ))`: both
sides are triangulated functors of `K` preserving the direct sums of objects of
`Loc(Dbc(X, Λ))`. -/
theorem isIso_baseChangeMap_of_localizingBoundedConstructible (sq : CommSq g' p' p g)
    (hsum : R((p)_*⟦Λ⟧).PreservesCoproductsOn.{u + 1} (localizingBoundedConstructible Λ X))
    (hsum' : R((p')_*⟦Λ⟧).PreservesCoproductsOn.{u + 1} (localizingBoundedConstructible Λ X'))
    (hpull : ∀ K : 𝔻(X), boundedConstructible (condensedRingObj Λ X) K →
      boundedConstructible (condensedRingObj Λ X') (L((g')^*⟦Λ⟧).obj K))
    (h : ∀ K : 𝔻(X), boundedConstructible (condensedRingObj Λ X) K →
      IsIso ((baseChangeMap Λ sq).app K))
    {K : 𝔻(X)} (hK : localizingBoundedConstructible Λ X K) :
    IsIso ((baseChangeMap Λ sq).app K) :=
  NatTrans.isIso_app_of_localizingClosure (baseChangeMap Λ sq)
    (P := boundedConstructible (condensedRingObj Λ X))
    (hsum.comp (Functor.preservesCoproductsOn_of_preservesColimitsOfShape L((g)^*⟦Λ⟧) ⊤)
      (fun _ _ ↦ trivial))
    ((Functor.preservesCoproductsOn_of_preservesColimitsOfShape L((g')^*⟦Λ⟧) _).comp hsum'
      (fun _ hM ↦ localizingBoundedConstructible_leftDerivedUpperStar Λ g' hpull hM))
    h hK

end AlgebraicGeometry.ProEtale.CondensedRing
