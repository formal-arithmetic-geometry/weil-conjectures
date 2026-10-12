module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Sheaf.CategoryTheory.ArrowsFunctor

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

/-- Finitely many isomorphisms out of fixed stage objects lift above that stage.
Source: Stacks Project, Sites, Tag 09YL, finite-diagram observation, and Categories,
Tag 04AX, the object and arrow description of filtered colimits.
(blueprint: lem-weil-pbc-filtered-colimit-finite-iso-lift)

Proof: Represent each prescribed target object and the hom and inverse of each E i
using surjectivity of the object and arrow cocones. Move these finitely many
representatives and j to a common stage. The images of their endpoints agree with
those of the fixed objects D i and the chosen target representatives. Eventual
equality in the object colimit, followed by a common refinement, aligns these
endpoints. Transporting the representative arrows along these equalities gives
arrows from the chosen targets to the transition images of D i, and back.
Their composites have identity images, because they represent inverse pairs.
Eventual equality in the arrow colimit makes both inverse equations hold after
another common refinement. These arrows are therefore stage isomorphisms t i,
with the required image of their hom. Naturality preserves the image equality
at every refinement. Finiteness concerns only the index, not the stage categories.
For an empty index take k = j and the identity transition; all family conditions
are vacuous. -/
theorem filteredColimit_finite_iso_lift
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (V : Cocone F) (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    {ι : Type u} [Finite ι] (j : J) (D : ι → F.obj j) (Z : ι → V.pt)
    (E : ∀ i, (V.ι.app j).toFunctor.obj (D i) ≅ Z i) :
    ∃ (k : J) (c : j ⟶ k) (D' : ι → F.obj k)
      (t : ∀ i, D' i ≅ (F.map c).toFunctor.obj (D i)),
      ∀ i, Arrow.mk ((V.ι.app k).toFunctor.map (t i).hom) = Arrow.mk (E i).inv := by
  sorry

end CategoryTheory
