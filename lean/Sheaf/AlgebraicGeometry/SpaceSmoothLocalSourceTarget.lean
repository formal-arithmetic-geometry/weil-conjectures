/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O1
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Smooth source-and-target locality on algebraic spaces

Source: Stacks Project, Descent on Spaces, Tag 06F8, definition-local-source-target
(blueprint: def-sfb-space-smooth-local-source-target).

Smoothness uses the existing compatible étale scheme-chart test. Point images use
field-valued point classes and common field extensions, without choosing representatives.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The three clauses of smooth locality on source-and-target: smooth precomposition,
smooth base change, and detection at each source point by a smooth diagram.
Source: Stacks Project, Tag 06F8, definition-local-source-target
(blueprint: def-sfb-space-smooth-local-source-target). -/
def IsSmoothLocalOnSourceAndTarget {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) : Prop :=
  (∀ {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z),
    MapIsLocally @Smooth f → P g → P (f ≫ g)) ∧
  (∀ {X Y Y' X' : AlgebraicSpace S} (f : X ⟶ Y) (b : Y' ⟶ Y)
      (a : X' ⟶ X) (f' : X' ⟶ Y'),
    IsPullback a f' f b → MapIsLocally @Smooth b → P f → P f') ∧
  ∀ {X Y : AlgebraicSpace S} (r : X ⟶ Y),
    P r ↔ ∀ x : Point X.obj.obj,
      ∃ (U V : AlgebraicSpace S) (a : U ⟶ X) (b : V ⟶ Y) (h : U ⟶ V),
        a ≫ r = h ≫ b ∧ MapIsLocally @Smooth a ∧ MapIsLocally @Smooth b ∧
          x ∈ pointImage a.hom.hom ∧ P h

end AlgebraicGeometry.AlgebraicSpace
