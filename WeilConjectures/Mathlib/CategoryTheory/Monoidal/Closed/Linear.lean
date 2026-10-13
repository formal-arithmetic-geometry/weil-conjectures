/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Linear

/-!
# Linearity of the internal hom in its first variable

In a monoidal closed category whose tensor product is `R`-linear, precomposition
`MonoidalClosed.pre f : ihom B ⟶ ihom A` with `f : A ⟶ B` is `R`-linear in `f`.
-/

@[expose] public section

namespace CategoryTheory.MonoidalClosed

open MonoidalCategory

variable {R : Type*} [Semiring R] {C : Type*} [Category* C] [Preadditive C] [Linear R C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear R C] [MonoidalClosed C]

/-- `uncurry` is `R`-linear. -/
lemma uncurry_smul {A X Y : C} (r : R) (g : Y ⟶ A ⟶[C] X) :
    uncurry (r • g) = r • uncurry g := by
  rw [uncurry_eq, uncurry_eq, MonoidalLinear.whiskerLeft_smul, Linear.smul_comp]

/-- Precomposition in the internal hom is `R`-linear. -/
lemma pre_smul {A B : C} (r : R) (f : B ⟶ A) (X : C) :
    (pre (r • f)).app X = r • (pre f).app X :=
  uncurry_injective (by
    rw [uncurry_smul, uncurry_pre, uncurry_pre, MonoidalLinear.smul_whiskerRight,
      Linear.smul_comp])

/-- The internal hom functor is `R`-linear in its first variable. -/
lemma internalHom_map_smul {A B : C} (r : R) (f : A ⟶ B) (X : C) :
    (internalHom.map (r • f).op).app X = r • (internalHom.map f.op).app X :=
  pre_smul r f X

end CategoryTheory.MonoidalClosed
