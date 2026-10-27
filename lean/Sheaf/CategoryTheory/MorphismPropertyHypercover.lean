/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q160
-/
module

public import Sheaf.CategoryTheory.ProperFaceMatchingObject
public import Mathlib.CategoryTheory.MorphismProperty.Basic

/-! # Hypercovers for a morphism property

Source: Stacks Project, Hypercoverings, Tag 0DER
(blueprint: def-sfb-morphism-property-hypercover).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.SimplicialObject

/-- A P-hypercover: every canonical proper-face matching arrow, in the slice, lies in P.
In degree zero this is the augmentation; in degree one its target is the fibre product
of the two zero terms over the base. A limiting cone is retained rather than choosing
matching objects. Since P contains isomorphisms in the theorem, the condition is
independent of the limiting cone.
Source: Stacks, Tag 0DER (blueprint: def-sfb-morphism-property-hypercover). -/
def IsMorphismPropertyHypercover {C : Type u} [Category.{v} C]
    (P : MorphismProperty C) {X : C} (U : SimplicialObject (Over X)) : Prop :=
  ∀ n : ℕ, ∃ (c : Cone (U.properFaceDiagram n)) (hc : IsLimit c),
    P (hc.lift (U.mapCone
      (((Over.forgetCocone (SimplexCategory.mk n)).whisker
        (SimplicialObject.properFaceProperty n).ι).op))).left

end CategoryTheory.SimplicialObject
