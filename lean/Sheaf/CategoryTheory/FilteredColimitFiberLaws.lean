/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import Sheaf.CategoryTheory.FilteredColimitHomCategory
public import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-! # Category laws on filtered arrow fibers -/

@[expose] public section

universe z

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Source: Stacks Project, Sites, proof of Tag 09YL, first paragraph,
and Categories, Section Tag 04AX.
(blueprint: lem-weil-pbc-filtered-colimit-fiber-laws).

Proof: An arbitrary element of a Hom fiber has a stage arrow representative.
For the identity laws choose such a representative and identify its endpoints with
the given objects. The two preservation formulas reduce the assertion to the stage
identity laws. For associativity choose representatives of the three arrows, move
them to a common stage, and use eventual equality in the object colimit to make
both middle endpoint equalities hold at a further stage. Both iterated composites
are then represented by the iterated composites at that stage, by the preservation
formula. Stage associativity equates them. Equality in a fiber is equality of its
underlying arrow colimit elements, since endpoint certificates are propositions.
Thus transporting endpoint equalities introduces no additional choice. The empty
object colimit case has no arrows and the assertions are vacuous. -/
theorem filteredColimit_fiber_laws
    (J : Type z) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{z, z})
    (i : ∀ X : colimit (F ⋙ Cat.objects), FilteredColimitHom F X X)
    (c : ∀ {X Y Z : colimit (F ⋙ Cat.objects)}, FilteredColimitHom F X Y →
      FilteredColimitHom F Y Z → FilteredColimitHom F X Z)
    (hi : ∀ (j : J) (X : F.obj j),
      i (colimit.ι (F ⋙ Cat.objects) j X) = filteredColimitHomι F j (𝟙 X))
    (hc : ∀ (j : J) (X Y Z : F.obj j) (f : X ⟶ Y) (g : Y ⟶ Z),
      c (filteredColimitHomι F j f) (filteredColimitHomι F j g) =
        filteredColimitHomι F j (f ≫ g)) :
    (∀ (X Y : colimit (F ⋙ Cat.objects)) (f : FilteredColimitHom F X Y),
      c (i X) f = f) ∧
    (∀ (X Y : colimit (F ⋙ Cat.objects)) (f : FilteredColimitHom F X Y),
      c f (i Y) = f) ∧
    (∀ (W X Y Z : colimit (F ⋙ Cat.objects))
      (f : FilteredColimitHom F W X) (g : FilteredColimitHom F X Y)
      (h : FilteredColimitHom F Y Z), c (c f g) h = c f (c g h)) := by sorry

end CategoryTheory
