/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q15 and Q73
-/
module

public import Sheaf.AlgebraicGeometry.OrdinaryResolutionRule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Uncontracted cartesian comparisons of ordinary blowup towers

Source: ILO, Travaux de Gabber, VIII 2.1.7--2.1.9, printed pp.87--88
(blueprint: def-per-ordinary-tower-cartesian-map).

The comparison retains the length, every level and the full extended center ideals.
Empty centers are retained. This is data specifying a pullback when it exists;
no flatness hypothesis or contraction is part of the definition.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- An uncontracted scheme-theoretic pullback of ordinary towers. The cast only identifies
finite index types of the equal lengths; no stage is deleted.
Source: ILO VIII 2.1.7--2.1.9, printed pp.87--88
(blueprint: def-per-ordinary-tower-cartesian-map). -/
structure OrdinaryTowerCartesianMap {X Y : Scheme.{u}} (h : Y ⟶ X)
    (A : OrdinaryBlowupTower X) (B : OrdinaryBlowupTower Y) where
  length_eq : B.length = A.length
  map : ∀ i : Fin (B.length + 1),
    B.level i ⟶ A.level (Fin.cast (congrArg Nat.succ length_eq) i)
  cartesian : ∀ i, IsPullback (map i) (B.toBase i)
    (A.toBase (Fin.cast (congrArg Nat.succ length_eq) i)) h
  arrows : ∀ i : Fin B.length,
    B.transition i.castSucc i.succ (le_of_lt i.castSucc_lt_succ) ≫ map i.castSucc =
      map i.succ ≫ A.transition (Fin.cast length_eq i).castSucc
        (Fin.cast length_eq i).succ (le_of_lt (Fin.cast length_eq i).castSucc_lt_succ)
  centers : ∀ i : Fin B.length,
    B.center i = (A.center (Fin.cast length_eq i)).comap (map i.castSucc)

end AlgebraicGeometry
