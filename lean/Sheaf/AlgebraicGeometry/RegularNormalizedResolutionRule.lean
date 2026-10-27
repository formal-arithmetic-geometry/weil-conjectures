/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q73
-/
module

public import Sheaf.AlgebraicGeometry.NormalizedTowerDescentData
public import Sheaf.AlgebraicGeometry.QEOrdinaryResolutionRule
public import Mathlib.Algebra.Field.ULift

/-!
# Regular-functorial normalized resolution rules

Source: ILO, Travaux de Gabber, VIII 2.2.3--2.2.8, 2.3.2--2.3.5 and
2.3.10--2.3.12 (blueprint: def-per-regular-normalized-resolution-rule).

The domain includes all reduced Noetherian quasi-excellent rational schemes,
including finite disjoint unions and the empty scheme. Inputs and regular
morphisms (flat, with geometrically regular fibres) are the existing
`QERationalResolutionInput` and `IsResolutionRegular`. The existing normalized
blowups supply the actual construction at each stage, with their defining ideals.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A finite normalized tower over its specified scheme, with coherent nonempty
nowhere dense centers and regular last scheme. Source: ILO VIII 2.2.5, 2.3.2
(blueprint: def-per-regular-normalized-resolution-rule). -/
structure NormalizedResolutionOver (X : Scheme.{u}) where
  length : ℕ
  tower : Monoscheme.NormalizedTower.{u} length
  initial : tower.level 0 ≅ X
  centers : ∀ i : Fin length,
    Set.Nonempty ((tower.center i).support : Set (tower.level i.castSucc)) ∧
      IsNowhereDense ((tower.center i).support : Set (tower.level i.castSucc))
  regularLast : tower.IsDesingularization

/-- Recursive regular pullback retains every center, including unit ideals.
The square at every level is cartesian. Source: ILO VIII 2.2.7--2.2.8
(blueprint: def-per-regular-normalized-resolution-rule). -/
structure RegularNormalizedPullback {n : ℕ}
    (T S : Monoscheme.NormalizedTower.{u} n) where
  lift : ∀ i : Fin (n + 1), S.level i ⟶ T.level i
  regular : ∀ i, IsResolutionRegular (lift i)
  centers : ∀ i : Fin n, S.center i = (T.center i).comap (lift i.castSucc)
  commutes : ∀ i : Fin n, S.arrow i ≫ lift i.castSucc = lift i.succ ≫ T.arrow i
  cartesian : ∀ i,
    IsPullback (lift i) (S.toFirst i) (T.toFirst i) (lift 0)

/-- The source tower is the contraction of the actual regular pullback of the
target tower. Contraction is the existing ordered-center contraction, deleting
exactly unit-center isomorphisms. Source: ILO VIII 2.3.4, 2.3.12(i)
(blueprint: def-per-regular-normalized-resolution-rule). -/
structure RegularNormalizedResolutionComparison {Y X : Scheme.{u}} (f : Y ⟶ X)
    (A : NormalizedResolutionOver X) (B : NormalizedResolutionOver Y) where
  pulled : Monoscheme.NormalizedTower.{u} A.length
  initial : pulled.level 0 ≅ Y
  pullback : RegularNormalizedPullback A.tower pulled
  base : pullback.lift 0 ≫ A.initial.hom = initial.hom ≫ f
  contraction : Monoscheme.NormalizedContraction pulled B.tower
  contractionBase : (contraction.iso 0).hom ≫
    eqToHom (congrArg B.tower.level contraction.first) ≫ B.initial.hom = initial.hom

/-- The comparison map after undoing the contraction isomorphism.
Source: ILO VIII 2.3.4 (blueprint: def-per-regular-normalized-resolution-rule). -/
noncomputable def RegularNormalizedResolutionComparison.levelMap
    {Y X : Scheme.{u}} {f : Y ⟶ X} {A : NormalizedResolutionOver X}
    {B : NormalizedResolutionOver Y} (c : RegularNormalizedResolutionComparison f A B)
    (i : Fin (A.length + 1)) :
    B.tower.level (c.contraction.index i) ⟶ A.tower.level i :=
  (c.contraction.iso i).inv ≫ c.pullback.lift i

/-- A single normalized desingularization rule on the entire domain, functorial
for all regular morphisms. Identity and composition are equations on both the
retained indices and the actual level maps. Finite disjoint unions are inputs
in their own right, rather than collections of independently contracted towers.
Source: ILO VIII 2.3.4--2.3.5, 2.3.10--2.3.12
(blueprint: def-per-regular-normalized-resolution-rule). -/
structure RegularFunctorialNormalizedResolution where
  resolution : ∀ X : QERationalResolutionInput.{u}, NormalizedResolutionOver X.scheme
  comparison : ∀ (X Y : QERationalResolutionInput.{u}) (f : Y.scheme ⟶ X.scheme),
    f ≫ X.structureMap = Y.structureMap → IsResolutionRegular f →
      RegularNormalizedResolutionComparison f (resolution X) (resolution Y)
  identityIndex : ∀ (X : QERationalResolutionInput.{u}) (f : X.scheme ⟶ X.scheme)
    (hf : f ≫ X.structureMap = X.structureMap) (hr : IsResolutionRegular f),
    f = 𝟙 X.scheme → ∀ i, (comparison X X f hf hr).contraction.index i = i
  identityMap : ∀ (X : QERationalResolutionInput.{u}) (f : X.scheme ⟶ X.scheme)
    (hf : f ≫ X.structureMap = X.structureMap) (hr : IsResolutionRegular f),
    f = 𝟙 X.scheme → ∀ i,
      HEq ((comparison X X f hf hr).levelMap i) (𝟙 ((resolution X).tower.level i))
  compositionIndex : ∀ (X Y Z : QERationalResolutionInput.{u})
    (f : Y.scheme ⟶ X.scheme) (g : Z.scheme ⟶ Y.scheme) (h : Z.scheme ⟶ X.scheme)
    (hf : f ≫ X.structureMap = Y.structureMap) (hg : g ≫ Y.structureMap = Z.structureMap)
    (hh : h ≫ X.structureMap = Z.structureMap)
    (rf : IsResolutionRegular f) (rg : IsResolutionRegular g)
    (rh : IsResolutionRegular h), h = g ≫ f → ∀ i,
      (comparison X Z h hh rh).contraction.index i =
        (comparison Y Z g hg rg).contraction.index ((comparison X Y f hf rf).contraction.index i)
  compositionMap : ∀ (X Y Z : QERationalResolutionInput.{u})
    (f : Y.scheme ⟶ X.scheme) (g : Z.scheme ⟶ Y.scheme) (h : Z.scheme ⟶ X.scheme)
    (hf : f ≫ X.structureMap = Y.structureMap) (hg : g ≫ Y.structureMap = Z.structureMap)
    (hh : h ≫ X.structureMap = Z.structureMap)
    (rf : IsResolutionRegular f) (rg : IsResolutionRegular g)
    (rh : IsResolutionRegular h), h = g ≫ f → ∀ i,
      HEq ((comparison X Z h hh rh).levelMap i)
        ((comparison Y Z g hg rg).levelMap ((comparison X Y f hf rf).contraction.index i) ≫
          (comparison X Y f hf rf).levelMap i)

end AlgebraicGeometry
