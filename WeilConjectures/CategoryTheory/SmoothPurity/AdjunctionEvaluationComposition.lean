/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.CategoryTheory.Normalized.NormalizedAdjunctionComposition

/-! # Evaluation of a composite left-adjoint extension

Source: the horizontal composition law for adjunction mates, Stacks 0FND.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Functor
namespace CategoryTheory
variable {X Y Z A B C : Type*}
  [Category X] [Category Y] [Category Z] [Category A] [Category B] [Category C]
  {F : X ⥤ Y} {U : Y ⥤ X} {G : Y ⥤ Z} {V : Z ⥤ Y} {H : X ⥤ Z} {W : Z ⥤ X}
  {Gx : X ⥤ A} {Gy : Y ⥤ B} {Gz : Z ⥤ C}
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : B ⥤ C} {R₂ : C ⥤ B}
  {L₃ : A ⥤ C} {R₃ : C ⥤ A}

end CategoryTheory
