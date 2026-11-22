/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteDg.RingedSiteDgModules

/-! Derived restriction descends from the literal dg restriction.

Source: the restriction part of Stacks sdga, Tags 0FT4 and 0FT5
(blueprint: lem-sfb-ringed-dg-restriction-descends-exact).

Restriction keeps the underlying complex, hence preserves quasi-isomorphisms.
The localization universal property supplies the functor and its
factorization isomorphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe c v u

open CategoryTheory

namespace CategoryTheory.RingedSiteDg

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{u} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-- The exact localization lift of literal restriction, with its fixed comparison. -/
structure RestrictionDescentData {O : Sheaf J CommRingCat.{u}}
    {A B : Algebra.{c, v, u} O} (φ : A ⟶ B)
    [DerivedStructure A] [DerivedStructure B] where
  restriction : Derived B ⥤ Derived A
  restrictionIso : Q B ⋙ restriction ≅ RingedSiteDg.restriction φ ⋙ Q A
  [restrictionShift : restriction.CommShift ℤ]
  restrictionExact : restriction.IsTriangulated

/-- Restriction retains the whole underlying complex, so it preserves quasi-isomorphisms.
Source: Stacks sdga, 0FT4
(blueprint: lem-sfb-ringed-dg-restriction-descends-exact). -/
theorem restriction_preserves_quasiisomorphisms
    {O : Sheaf J CommRingCat.{u}} {A B : Algebra.{c, v, u} O} (φ : A ⟶ B)
    {M N : Module B} (f : M ⟶ N) (hf : quasiIsomorphisms B f) :
    quasiIsomorphisms A ((RingedSiteDg.restriction φ).map f) := by
  exact hf

/-- The literal descended restriction, constructed by localization.
Source: Stacks sdga, 0FT5
(blueprint: lem-sfb-ringed-dg-restriction-descends-exact). -/
def derivedRestriction
    {O : Sheaf J CommRingCat.{u}} {A B : Algebra.{c, v, u} O} (φ : A ⟶ B) :
    Derived B ⥤ Derived A :=
  Localization.lift (RingedSiteDg.restriction φ ⋙ Q A)
    (fun _ _ f hf ↦ Localization.inverts (Q A) (quasiIsomorphisms A) _
      (restriction_preserves_quasiisomorphisms φ f hf)) (Q B)

/-- The fixed factorization of the literal descended restriction.
Source: Stacks sdga, 0FT5
(blueprint: lem-sfb-ringed-dg-restriction-descends-exact). -/
def derivedRestrictionIso
    {O : Sheaf J CommRingCat.{u}} {A B : Algebra.{c, v, u} O} (φ : A ⟶ B) :
    Q B ⋙ derivedRestriction φ ≅ RingedSiteDg.restriction φ ⋙ Q A :=
  Localization.fac (RingedSiteDg.restriction φ ⋙ Q A)
    (fun _ _ f hf ↦ Localization.inverts (Q A) (quasiIsomorphisms A) _
      (restriction_preserves_quasiisomorphisms φ f hf)) (Q B)

end CategoryTheory.RingedSiteDg
