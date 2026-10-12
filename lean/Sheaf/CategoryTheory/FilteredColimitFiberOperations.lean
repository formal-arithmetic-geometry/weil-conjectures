/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import Sheaf.CategoryTheory.FilteredColimitHomCategory
public import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-! # Identity and composition on filtered arrow fibers -/

@[expose] public section

universe z

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Source: Stacks Project, Sites, proof of Tag 09YL, first paragraph,
and Categories, Section Tag 04AX.
(blueprint: lem-weil-pbc-filtered-colimit-fiber-operations).

Proof: Represent an object in the object colimit by a stage object and send its
identity to the arrow colimit. Represent two composable fiber elements by stage
arrows. Move the representatives to a common stage. Their middle endpoints agree
in the object colimit, so the filtered-colimit equality criterion makes them equal
at a further stage. Transport along this equality and compose at that stage.
Independence of all choices follows by moving two choices to a common stage and
using eventual equality for their arrows and endpoints; transition functors preserve
identities and composition. The resulting arrow has the required endpoints, so lies
in the required fiber. The formulas for stage identities and composites follow by
choosing the stage itself for the representatives. Empty stage categories give no
objects requiring identities; otherwise each object has a representative. -/
theorem filteredColimit_fiber_operations
    (J : Type z) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{z, z}) :
    let O := colimit (F ⋙ Cat.objects)
    ∃ (i : ∀ X : O, FilteredColimitHom F X X)
      (c : ∀ {X Y Z : O}, FilteredColimitHom F X Y →
        FilteredColimitHom F Y Z → FilteredColimitHom F X Z),
      (∀ (j : J) (X : F.obj j),
        i (colimit.ι (F ⋙ Cat.objects) j X) = filteredColimitHomι F j (𝟙 X)) ∧
      (∀ (j : J) (X Y Z : F.obj j) (f : X ⟶ Y) (g : Y ⟶ Z),
        c (filteredColimitHomι F j f) (filteredColimitHomι F j g) =
          filteredColimitHomι F j (f ≫ g)) := by sorry

end CategoryTheory
