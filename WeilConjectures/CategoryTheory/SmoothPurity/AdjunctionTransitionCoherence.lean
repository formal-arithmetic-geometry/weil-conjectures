/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.CategoryTheory.Normalized.NormalizedAdjunctionComposition

/-! # Transition coherence from a right-adjoint cocone

Source: the horizontal composition law for adjunction mates, Stacks 0FND.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Functor
namespace CategoryTheory
variable {X Y A B C D : Type*}
  [Category X] [Category Y] [Category A] [Category B] [Category C] [Category D]
  {F : X ⥤ Y} {U : Y ⥤ X}
  {Ga : X ⥤ A} {Gb : X ⥤ B}
  {Va : Y ⥤ A} {Vb : Y ⥤ B} {Vm : Y ⥤ C} {Vn : Y ⥤ D}
  {Lp : A ⥤ C} {Rp : C ⥤ A} {Lq : B ⥤ D} {Rq : D ⥤ B}
  {Lh : D ⥤ C} {Rh : C ⥤ D} {Lk : B ⥤ A} {Rk : A ⥤ B}
  {Lt : B ⥤ C} {Rt : C ⥤ B}

end CategoryTheory
