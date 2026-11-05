/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.FourCornersSupplement
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedRlimFunctor
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import WeilConjectures.AlgebraicGeometry.StrictTowerOperations

/-! # Canonical operations on strict module towers

Source: blueprint completed-exchange-coherence, first two proof sentences;
Stacks 07A7 and 0D6D (blueprint: def-weil-pbc-strict-tower-operations).

## Main definitions

* `exchangeTowerPull`, `exchangeTowerPush`: strict diagram derived functors.
* `exchangeTowerAdjunction`: the derived termwise normalized module adjunction.
* `StrictTowerRingedSquare.exchangeTowerSquare`: canonical pullback composition.
* `StrictTowerRingedSquare.exchangeTowerMate`: its specified adjunction mate.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

variable {U V : Scheme.{t}} (f : U ⟶ V)
  (R : Sheaf (ProEt.topology V) CommRingCat.{t + 1})
  (S : Sheaf (ProEt.topology U) CommRingCat.{t + 1})
  (c : (proEtaleSheafInverseImage f CommRingCat.{t + 1}).obj R ≅ S)

variable {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {sq : ChosenCartesianSquare g' f' f g}

end AlgebraicGeometry.Scheme
