/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q44
-/
module

public import Sheaf.AlgebraicGeometry.MonoschemeToricRealization
public import Sheaf.AlgebraicGeometry.ToricMonoidComparison
public import Sheaf.AlgebraicGeometry.NormalizedTowerDescentData
public import Mathlib.Algebra.Field.ULift

/-!
# Data for centered toric tower lifts

Source: ILO, Travaux de Gabber, Exposé VIII, 3.2.19 and Theorem 3.2.20,
p.106, using 3.2.12(ii), 3.2.15 and 3.2.18
(blueprint: def-trf-centered-toric-tower-lift-data).

Uniqueness is an isomorphism of centered monoscheme towers inducing the specified
realization identifications. It is not equality of presentations of sheafed spaces.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Monoscheme

/-- The original component tori preserve every center of the given normalized tower.
The lifted action is over the original monomial action, and preservation is equality
of ideal sheaves, not of their radicals. Products are restricted to the component.
Source: ILO VIII 3.2.15 and 3.2.19
(blueprint: def-trf-centered-toric-tower-lift-data). -/
def NormalizedTower.HasEquivariantToricCenters {n : ℕ} (M : Fine.{u})
    (T : NormalizedTower.{u} n) (e₀ : T.level 0 ≅ realization (ULift.{u} ℚ) M) : Prop :=
  ∀ (C : ToricComponent M) (i : Fin n),
    ∃ μ : toricActionDomain (ULift.{u} ℚ) C
        (T.toFirst i.castSucc ≫ e₀.hom) ⟶ T.level i.castSucc,
      μ ≫ T.toFirst i.castSucc ≫ e₀.hom =
        toricActionBase (ULift.{u} ℚ) C (T.toFirst i.castSucc ≫ e₀.hom) ∧
      (T.center i).comap μ = (T.center i).comap
        (pullback.snd _ _ ≫ pullback.fst _ _)

/-- A centered lift retains every stage and uses the canonical monomial realization
of every arrow. `Tower.blowup` supplies the exact saturated affine blowup charts and
nonempty coherent monoid centers. Finiteness of affine covers is part of `Fine`.
The comparison is over the original base with its unchanged dense component tori.
Source: ILO VIII 3.2.18--3.2.20
(blueprint: def-trf-centered-toric-tower-lift-data). -/
structure CenteredToricTowerLift {n : ℕ} (M : Fine.{u})
    (T : NormalizedTower.{u} n) (e₀ : T.level 0 ≅ realization (ULift.{u} ℚ) M) where
  tower : Tower.{u} n
  base : tower.level 0 = M
  torsionFree : ∀ i, (tower.level i).IsTorsionFree
  iso : ∀ i, realization (ULift.{u} ℚ) (tower.level i) ≅ T.level i
  initial : (iso 0).hom ≫ e₀.hom =
    eqToHom (congrArg (realization (ULift.{u} ℚ)) base)
  centers : ∀ i : Fin n, ringIdeal (ULift.{u} ℚ) (tower.center i) =
    (T.center i).comap (iso i.castSucc).hom
  arrows : ∀ i : Fin n,
    realizationMap (ULift.{u} ℚ) (tower.arrow i) ≫ (iso i.castSucc).hom =
      (iso i.succ).hom ≫ T.arrow i
  equivariant : ∀ i : Fin (n + 1),
    IsToricComparison (ULift.{u} ℚ)
      ((iso i).hom ≫ T.toFirst i ≫ e₀.hom) (T.toFirst i ≫ e₀.hom) (iso i)

/-- The canonical centered identification between two lifts fixes the specified base,
commutes with arrows, preserves the actual ideals, and induces the specified scheme
identifications by the monomial realization. It compares monoscheme maps, not arbitrary
scheme isomorphisms; uniqueness of this family is the intended uniqueness of descent.
Source: ILO VIII 3.2.14--3.2.20
(blueprint: def-trf-centered-toric-tower-lift-data). -/
def CenteredToricTowerLift.IsCenteredIdentification {n : ℕ} {M : Fine.{u}}
    {T : NormalizedTower.{u} n} {e₀ : T.level 0 ≅ realization (ULift.{u} ℚ) M}
    (L L' : CenteredToricTowerLift M T e₀)
    (e : ∀ i : Fin (n + 1), (L.tower.level i).space ≅ (L'.tower.level i).space) : Prop :=
  (e 0).hom = eqToHom (congrArg Fine.space (L.base.trans L'.base.symm)) ∧
  (∀ i : Fin n,
    (L.tower.arrow i).map ≫ (e i.castSucc).hom =
      (e i.succ).hom ≫ (L'.tower.arrow i).map) ∧
  (∀ i : Fin n,
    L.tower.center i = pullbackAlong (e i.castSucc).hom (L'.tower.center i)) ∧
  ∀ i : Fin (n + 1), ∃ f : Hom (L.tower.level i) (L'.tower.level i),
    f.map = (e i).hom ∧
      realizationMap (ULift.{u} ℚ) f ≫ (L'.iso i).hom = (L.iso i).hom

end AlgebraicGeometry.Monoscheme
