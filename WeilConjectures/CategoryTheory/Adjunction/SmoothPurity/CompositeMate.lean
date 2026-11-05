/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# The Hom formula for the mate of a transition between right adjoints

Source: Zheng, Construction 4.1, p. 21, the adjunction formula for truncation maps.
(blueprint: lem-pur-evaluation-transition-mate).
-/

@[expose] public section
set_option autoImplicit false
universe uA vA uB vB uS vS
namespace CategoryTheory.Adjunction
open CategoryTheory CategoryTheory.Category
variable {A : Type uA} {B : Type uB} {S : Type uS}
  [Category.{vA} A] [Category.{vB} B] [Category.{vS} S]
  {T : A ⥤ B} {R : B ⥤ A} {E₁ : B ⥤ S} {e₁ : S ⥤ B}
  {E₂ : A ⥤ S} {e₂ : S ⥤ A}

end CategoryTheory.Adjunction
