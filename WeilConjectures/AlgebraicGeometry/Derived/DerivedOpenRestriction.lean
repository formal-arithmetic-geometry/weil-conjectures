/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.BaseChange.Derived
import WeilConjectures.SixFunctors.BaseChange.EtaleDerived

/-!
# Derived direct image restricted to an open

Source: Stacks Project, Tags 03S2, 03F3, 05TI and 05TH.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Restriction of derived direct image to an open subscheme is the derived direct image
of the restriction, naturally in the bounded-below complex of module sheaves over any
commutative ring `Λ`.
The transformation is the canonical derived exchange map, not an arbitrary isomorphism. -/
theorem isIso_derivedBaseChangeMapPlus_of_openImmersion_of_commRing
    (Λ : Type (u + 1)) [CommRing Λ]
    {T S U V : Scheme.{u}} (f : T ⟶ S) (a : U ⟶ S)
    (b : V ⟶ T) (fU : V ⟶ U) [IsOpenImmersion a]
    (sq : ChosenCartesianSquare b fU f a) :
    IsIso (derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq) := by
  exact isIso_derivedBaseChangeMapPlus_of_etale Λ
    (IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd)

/-- The finite-coefficient case of
`isIso_derivedBaseChangeMapPlus_of_openImmersion_of_commRing`, kept for its existing users. -/
theorem isIso_derivedBaseChangeMapPlus_of_openImmersion
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {T S U V : Scheme.{u}} (f : T ⟶ S) (a : U ⟶ S)
    (b : V ⟶ T) (fU : V ⟶ U) [IsOpenImmersion a]
    (sq : ChosenCartesianSquare b fU f a) :
    IsIso (derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq) :=
  isIso_derivedBaseChangeMapPlus_of_openImmersion_of_commRing Λ f a b fU sq

end AlgebraicGeometry.Etale
