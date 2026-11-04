/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Functor
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Naturality of the internal hom comparison of a lax monoidal functor

The comparison map `G [A, B] ⟶ [G A, G B]` of a lax monoidal functor
(`CategoryTheory.Functor.LaxMonoidal.ihomComparison`) is natural in `A`
(`CategoryTheory.Functor.LaxMonoidal.map_pre_app_comp_ihomComparison`).
-/

@[expose] public section

namespace CategoryTheory.Functor.LaxMonoidal

open MonoidalCategory

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  [MonoidalClosed C] [MonoidalClosed D] (G : C ⥤ D) [G.LaxMonoidal]

/-- The comparison map `G [A, B] ⟶ [G A, G B]` is natural in `A`:
```
   G [A, B] ──────▶ [G A, G B]
      │                 │
 G [f, B]           [G f, G B]
      ▼                 ▼
   G [A', B] ─────▶ [G A', G B]
```
-/
@[reassoc]
lemma map_pre_app_comp_ihomComparison {A A' : C} (f : A' ⟶ A) (B : C) :
    G.map ((MonoidalClosed.pre f).app B) ≫ (ihomComparison G A').natTrans.app B =
      (ihomComparison G A).natTrans.app B ≫
        (MonoidalClosed.pre (G.map f)).app (G.obj B) := by
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_pre_app, MonoidalClosed.uncurry_eq, MonoidalClosed.uncurry_eq,
    MonoidalCategory.whiskerLeft_comp_assoc, ihomComparison_ev, μ_natural_right_assoc,
    ← G.map_comp, ← MonoidalClosed.uncurry_eq, MonoidalClosed.uncurry_pre,
    ihomComparison_ev, μ_natural_left_assoc, ← G.map_comp]

end CategoryTheory.Functor.LaxMonoidal
