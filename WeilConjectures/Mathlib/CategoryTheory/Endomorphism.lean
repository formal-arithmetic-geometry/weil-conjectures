/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Endomorphism

/-!
# Underlying morphisms of the unit and inverses in `Aut X`
-/

@[expose] public section

namespace CategoryTheory.Aut

variable {C : Type*} [Category* C] (X : C)

@[simp]
lemma one_hom : (1 : Aut X).hom = 𝟙 X :=
  rfl

variable {X}

@[simp]
lemma inv_hom (f : Aut X) : f⁻¹.hom = f.inv :=
  rfl

end CategoryTheory.Aut
