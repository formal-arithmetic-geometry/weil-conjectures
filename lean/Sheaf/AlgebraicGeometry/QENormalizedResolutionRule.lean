/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q157
-/
module

public import Sheaf.AlgebraicGeometry.NormalizedTowerDescentData
public import Sheaf.AlgebraicGeometry.RegularSchemeMorphism
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Sheaf.RingTheory.ExcellentRing
public import Mathlib.Algebra.Field.ULift
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-! # Regular-functorial normalized resolution rules

Source: ILO, Travaux de Gabber, VIII 2.2.3--2.2.9, 2.3.2--2.3.5 and
2.3.9--2.3.12 (blueprint: def-per-qe-normalized-resolution-rule).

The normalized towers and their ordered contractions are the published constructions.
A regular pullback is cartesian at every level; unit centers, rather than all
isomorphism stages, are deleted. No finiteness condition is imposed on a regular map.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

open Monoscheme

/-- Reduced Noetherian quasi-excellent schemes over the rationals, including empty and
disconnected schemes. No finite-type or separation hypothesis is imposed.
Source: ILO VIII 2.3.9--2.3.12
(blueprint: def-per-qe-normalized-resolution-rule). -/
structure QEResolutionInput where
  scheme : Scheme.{u}
  structureMap : scheme ⟶ Spec (.of (ULift.{u} ℚ))
  reduced : IsReduced scheme
  noetherian : IsNoetherian scheme
  quasiExcellent : ∀ U : scheme.affineOpens, IsQuasiExcellent Γ(scheme, U.1)

/-- The normal members of the same input class; normality is stalkwise normal-domain
normality and does not require irreducibility or nonemptiness.
Source: ILO VIII 2.2.1 and 2.3.12(i)
(blueprint: def-per-qe-normalized-resolution-rule). -/
def NormalQEResolutionInput : Type (u + 1) :=
  {X : QEResolutionInput.{u} // ∀ x : X.scheme,
    IsDomain (X.scheme.presheaf.stalk x) ∧ IsIntegrallyClosed (X.scheme.presheaf.stalk x)}

/-- A finite normalized resolution, based at its input by an isomorphism. Centers are
coherent modules, with nonempty nowhere dense zero schemes, and the last scheme is regular.
Source: ILO VIII 2.2.5 and 2.3.2
(blueprint: def-per-qe-normalized-resolution-rule). -/
structure QENormalizedResolutionTower (X : Scheme.{u}) where
  length : ℕ
  tower : NormalizedTower.{u} length
  initial : tower.level 0 ≅ X
  coherent : ∀ i : Fin length,
    RingedSpace.IsCoherent (tower.level i.castSucc).toRingedSpace (tower.center i).toModules
  nonempty : ∀ i : Fin length,
    Set.Nonempty ((tower.center i).support : Set (tower.level i.castSucc))
  nowhereDense : tower.HasNowhereDenseCenters
  regular : tower.IsDesingularization

/-- The composite to the specified input, using the existing recursive composite.
Source: ILO VIII 2.2.5 (blueprint: def-per-qe-normalized-resolution-rule). -/
def QENormalizedResolutionTower.toBase {X : Scheme.{u}} (A : QENormalizedResolutionTower X)
    (i : Fin (A.length + 1)) : A.tower.level i ⟶ X :=
  A.tower.toFirst i ≫ A.initial.hom

/-- A recursively pulled-back tower followed by its ordered unit-ideal contraction.
The cartesian squares and the extended ideal equalities specify the actual pullback.
The additional unit-isomorphism clause ensures deletion is exactly by unit ideal,
including when a proper invertible ideal also has an isomorphism as its blowup.
Source: ILO VIII 2.2.7--2.2.9, 2.3.4--2.3.5
(blueprint: def-per-qe-normalized-resolution-rule). -/
structure QENormalizedResolutionComparison {X Y : Scheme.{u}} (h : Y ⟶ X)
    (A : QENormalizedResolutionTower X) (B : QENormalizedResolutionTower Y) where
  pulled : NormalizedTower.{u} A.length
  initial : pulled.level 0 ≅ Y
  lift : ∀ i, pulled.level i ⟶ A.tower.level i
  base : lift 0 ≫ A.initial.hom = initial.hom ≫ h
  cartesian : ∀ i, IsPullback (lift i) (pulled.toFirst i ≫ initial.hom) (A.toBase i) h
  centers : ∀ i : Fin A.length,
    pulled.center i = (A.tower.center i).comap (lift i.castSucc)
  arrows : ∀ i : Fin A.length,
    pulled.arrow i ≫ lift i.castSucc = lift i.succ ≫ A.tower.arrow i
  unit_isIso : ∀ i : Fin A.length, pulled.center i = ⊤ → IsIso (pulled.arrow i)
  contraction : NormalizedContraction pulled B.tower
  contraction_base : (contraction.iso 0).hom ≫
    eqToHom (congrArg B.tower.level contraction.first) ≫ B.initial.hom = initial.hom

/-- The comparison map from a surviving level to the corresponding original level.
Source: ILO VIII 2.3.4 (blueprint: def-per-qe-normalized-resolution-rule). -/
noncomputable def QENormalizedResolutionComparison.levelMap {X Y : Scheme.{u}}
    {h : Y ⟶ X} {A : QENormalizedResolutionTower X} {B : QENormalizedResolutionTower Y}
    (c : QENormalizedResolutionComparison h A B) (i : Fin (A.length + 1)) :
    B.tower.level (c.contraction.index i) ⟶ A.tower.level i :=
  (c.contraction.iso i).inv ≫ c.lift i

/-- One simultaneous rule on a specified family of inputs, with canonical regular
pullbacks, identity and composition laws on counts and actual level maps, no deletions
for surjective maps, and the trivial tower on an empty input. The two applications are
all quasi-excellent inputs and their normal members. The chosen rational structures
impose no extra condition on morphisms: morphisms between rational schemes are over ℚ.
Source: ILO VIII 2.3.4--2.3.5 and 2.3.12(i)
(blueprint: def-per-qe-normalized-resolution-rule). -/
structure RegularNormalizedResolutionRule (I : Type v) (base : I → Scheme.{u}) where
  tower : ∀ X : I, QENormalizedResolutionTower (base X)
  comparison : ∀ (X Y : I) (h : base Y ⟶ base X), IsRegularSchemeMorphism h →
    QENormalizedResolutionComparison h (tower X) (tower Y)
  empty : ∀ X : I, IsEmpty (base X) → (tower X).length = 0
  identityIndex : ∀ (X : I) (hr : IsRegularSchemeMorphism (𝟙 (base X))) i,
    (comparison X X (𝟙 _) hr).contraction.index i = i
  identityMap : ∀ (X : I) (hr : IsRegularSchemeMorphism (𝟙 (base X))) i,
    HEq ((comparison X X (𝟙 _) hr).levelMap i) (𝟙 ((tower X).tower.level i))
  compositionIndex : ∀ (X Y Z : I) (h : base Y ⟶ base X) (g : base Z ⟶ base Y)
    (hr : IsRegularSchemeMorphism h) (gr : IsRegularSchemeMorphism g)
    (ghr : IsRegularSchemeMorphism (g ≫ h)) i,
    (comparison X Z (g ≫ h) ghr).contraction.index i =
      (comparison Y Z g gr).contraction.index ((comparison X Y h hr).contraction.index i)
  compositionMap : ∀ (X Y Z : I) (h : base Y ⟶ base X) (g : base Z ⟶ base Y)
    (hr : IsRegularSchemeMorphism h) (gr : IsRegularSchemeMorphism g)
    (ghr : IsRegularSchemeMorphism (g ≫ h)) i,
    HEq ((comparison X Z (g ≫ h) ghr).levelMap i)
      ((comparison Y Z g gr).levelMap ((comparison X Y h hr).contraction.index i) ≫
        (comparison X Y h hr).levelMap i)
  surjective_no_deletion : ∀ (X Y : I) (h : base Y ⟶ base X)
    (hr : IsRegularSchemeMorphism h), Surjective h →
      Function.Injective (comparison X Y h hr).contraction.index

end AlgebraicGeometry
