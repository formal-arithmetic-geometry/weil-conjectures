module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Sheaf.CategoryTheory.ArrowsFunctor
public import Sheaf.CategoryTheory.FinitePrecoverage

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

/-- Stage representation of an isomorphism in a filtered colimit category.
Source: Stacks Project, Sites, Tag 09YL.
(blueprint: lem-weil-pbc-filtered-colimit-iso-presieve-representation)

Proof: Represent the arrow and its inverse in the arrow colimit. Filteredness gives
one stage containing both representatives and all endpoint equalities. The two
inverse equations are equalities in the arrow colimit, hence become equalities at
a further common stage by the filtered colimit equality criterion. The resulting
stage arrow is an isomorphism; transporting its singleton along the target
identification gives the singleton of the original arrow.
-/
theorem filtered_colimit_iso_presieve_representation
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (P : ∀ j : J, Precoverage (F.obj j))
    [∀ j, (P j).HasIsos]
    (V : Cocone F)
    (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    {S T : V.pt} (f : S ⟶ T) [IsIso f] :
    ∃ (j : J) (X : F.obj j) (R : Presieve X)
      (h : (V.ι.app j).toFunctor.obj X = T),
      R ∈ P j X ∧ h ▸ R.map (V.ι.app j).toFunctor = Presieve.singleton f := by
  sorry

end CategoryTheory
