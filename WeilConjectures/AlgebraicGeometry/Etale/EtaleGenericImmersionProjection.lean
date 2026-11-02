/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekBaseChange
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjectionBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence

/-! # Projection formula for an immersion extension by zero

Source: Stacks Project, Tags 0E8I, 0GL1, 03S6 and 0A45
(blueprint: lem-sf-etale-generic-immersion-projection).

The comparison is the open projection inverse followed by the closed direct-image
projection map, with symmetries and the pullback-composition comparison. The theorem
includes its isomorphism property, naturality in both complexes, and the Cartesian
base-change equation using the composite of open base change and closed finite exchange.
-/

@[expose] public section
set_option autoImplicit false
universe u u'

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The functor `Rs_! = j_! Ri_*` for the chosen closed-then-open factorization.
Source: Stacks Project, Tags 0E8I and 0A45
(blueprint: lem-sf-etale-generic-immersion-projection). -/
noncomputable abbrev immersionLowerShriek
    (A : Type (u + 1)) [CommRing A]
    {S U X : Scheme.{u}} (i : S ⟶ U) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] :
    DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  R((i)_*[ModuleCat.{u + 1} A]) ⋙ D((j)_!open[ModuleCat.{u + 1} A])

attribute [local instance] _root_.DerivedCategory.braidedCategory'

section Coefficients

variable (B : Type u') [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
  [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
  [UpperStarPreservesFlat B]
  {FC : B → B → Type*} {CC : B → Type (u + 1)}
  [∀ (P Q : B), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} B FC]
  [(CategoryTheory.forget B).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget B)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget B)]

section BaseChange

variable [HasSmallSiteSheafify B]
  {S U X S' U' X' : Scheme.{u}}
  {i : S ⟶ U} {j : U ⟶ X} {i' : S' ⟶ U'} {j' : U' ⟶ X'}
  {gS : S' ⟶ S} {gU : U' ⟶ U} {gX : X' ⟶ X}
  [IsOpenImmersion j] [IsOpenImmersion j']
  (hi : IsPullback gS i' i gU) (hj : IsPullback gU j' j gX)

local notation "I" => R((i)_*[B])
local notation "I'" => R((i')_*[B])
local notation "J" => D((j)_!open[B])
local notation "J'" => D((j')_!open[B])
local notation "Fi" => L((i)^*[B])
local notation "Fi'" => L((i')^*[B])
local notation "Fj" => L((j)^*[B])
local notation "Fj'" => L((j')^*[B])
local notation "Gx" => L((gX)^*[B])
local notation "Gu" => L((gU)^*[B])
local notation "Gs" => L((gS)^*[B])
local notation "ei" => derivedBaseChangeMap B hi.toCommSq
local notation "bj" => Iso.inv (derivedOpenImmersionLowerShriekBaseChangeIso B hj)
local notation "si" => derivedSquareUpperStarIso B hi.toCommSq
local notation "sj" => derivedSquareUpperStarIso B hj.toCommSq
local notation "sc" => derivedSquareUpperStarIso B (hi.toCommSq.vert_comp hj.toCommSq)
local notation "ci" => leftDerivedUpperStarComp B i j
local notation "ci'" => leftDerivedUpperStarComp B i' j'
local notation "pi" => rightDerivedLowerStarProjectionMap B i
local notation "pi'" => rightDerivedLowerStarProjectionMap B i'
local notation "oj'" => Iso.inv (derivedOpenImmersionLowerShriekProjectionIso B j')

omit [UpperStarPreservesFlat B] in
omit [UpperStarPreservesFlat B] [HasSmallSiteSheafify B]
  [IsOpenImmersion j] [IsOpenImmersion j'] in
omit [UpperStarPreservesFlat B] [HasSmallSiteSheafify B]
  [IsOpenImmersion j] [IsOpenImmersion j'] in
omit [HasSmallSiteSheafify B] in
omit [HasSmallSiteSheafify B] [IsOpenImmersion j] [IsOpenImmersion j'] in
end BaseChange

end Coefficients

end AlgebraicGeometry.Etale
