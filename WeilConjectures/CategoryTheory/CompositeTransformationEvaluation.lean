/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Whiskering

/-! Evaluation of a transformation between composite functors with explicit endpoint objects.
Source: the definition of natural-transformation components.
(blueprint: def-ct-composite-transformation-evaluation).
-/

@[expose] public section
set_option autoImplicit false

namespace CategoryTheory

variable {C D E B : Type*} [Category C] [Category D] [Category E] [Category B]

/-- Evaluate a transformation with the component's endpoint objects written explicitly.
Source: functor composition and natural-transformation evaluation.
(blueprint: def-ct-composite-transformation-evaluation). -/
def evaluateCompositeTransformation
    (I : C ⥤ D) (F : D ⥤ E) (G : E ⥤ B) (H : D ⥤ B)
    (t : I ⋙ F ⋙ G ⟶ I ⋙ H) (M : C) :
    G.obj (F.obj (I.obj M)) ⟶ H.obj (I.obj M) := t.app M

end CategoryTheory
