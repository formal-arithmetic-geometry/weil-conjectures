/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import Sheaf.CategoryTheory.ArrowsFunctor
public import Mathlib.CategoryTheory.Limits.Types.Filtered

/-! # The category structure on the filtered object colimit -/

@[expose] public section

universe z

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Source: Stacks Project, Sites, proof of Tag 09YL, first paragraph, and
Categories, Section Tag 04AX (filtered colimits of sets).
(blueprint: lem-weil-pbc-filtered-colimit-category-structure).

Proof: Let A be the filtered colimit of the sets of stage arrows. The source and
target maps to the object colimit O descend by their compatibility with transition
functors. Identities descend in the same way. Every pair of composable arrows in A
has representatives at a common stage. The equality of their middle objects in O
holds at a further stage by the filtered-colimit equality criterion. Compose there.
Changing representatives does not change the resulting element of A: place both
pairs at a common further stage and use eventual equality on the finitely many
arrows and endpoint equalities. The identity laws and associativity follow by
representing the finitely many arrows at one stage where their endpoint equalities
hold, and applying the corresponding category laws there.

Define Hom(X,Y) to be the arrows in A whose source is X and target is Y. These
fibres, with the descended operations, define a category on O. An arrow with its
endpoints is equivalent to an element of A, giving the required equivalence from
the chosen set colimit cocone to Arrow O. Each stage functor sends an object and
an arrow to its colimit class. Its identity and composition laws follow from the
construction. Compatibility with transition functors follows from the cocone laws
on objects and arrows, and equality of functors follows by extensionality. -/
theorem filteredColimit_category_structure
    (J : Type z) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{z, z}) :
    let O := colimit (F ⋙ Cat.objects)
    ∃ (s : Category.{z} O),
    letI := s
    ∃ V : ∀ j : J, F.obj j ⥤ O,
      (∀ (j : J) (X : F.obj j), (V j).obj X = colimit.ι (F ⋙ Cat.objects) j X) ∧
      (∀ (j k : J) (f : j ⟶ k), (F.map f).toFunctor ⋙ V k = V j) ∧
      (∃ (a : Cocone (F ⋙ Cat.arrows)) (e : a.pt ≃ Arrow O),
        Nonempty (IsColimit a) ∧
          ∀ (j : J) (f : Arrow (F.obj j)),
            e (a.ι.app j f) = (V j).mapArrow.obj f) := by
  sorry

end CategoryTheory
