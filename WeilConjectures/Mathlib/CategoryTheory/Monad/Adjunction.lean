/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Monad.Adjunction

/-!
# Adjunctions whose left adjoint is isomorphic to the identity

If the left adjoint `L` of an adjunction `L ⊣ R` on a category `C` is isomorphic to the identity,
then so is `R`, and the unit and counit are isomorphisms.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

variable {C : Type*} [Category C] {L R : C ⥤ C}

end CategoryTheory.Adjunction
