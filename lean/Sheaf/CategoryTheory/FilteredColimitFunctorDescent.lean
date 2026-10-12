module

public import Sheaf.CategoryTheory.ArrowsFunctor
public import Mathlib.CategoryTheory.Limits.IsLimit
public import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Types.Filtered

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Source: Stacks Project, Sites, proof of Tag 09YL, the construction of the
filtered colimit category; the universal property verification is written here.
(blueprint: lem-weil-pbc-filtered-colimit-functor-descent).

Proof: send an object represented at stage j to its image under v j, and an arrow
represented at stage j to its image under v j. Compatibility makes these maps
well-defined: equal representatives agree at a common later stage by the equality
criterion for filtered colimits of sets. Object and arrow representatives exist
by the two set-colimit hypotheses. Source and target of the resulting arrow are
the chosen images of its endpoints, since the stage functors respect endpoints.
To verify identities represent the object at one stage. For composition represent
the two arrows at a common stage. Their middle endpoints have equal images in the
object colimit; after passing to a further stage those endpoints are equal, so
composition is represented by their composite there. Functoriality of v at that
stage proves preservation of composition. The defining representative formulas
give (L.ι.app j).toFunctor ⋙ V = v j, including equality on objects and arrows.
The construction uses only the small source categories; D may have larger object
and hom universes. -/
theorem exists_filteredColimit_functor_descent
    (J : Type u) [SmallCategory J] [IsFiltered J]
    (F : J ⥤ Cat.{u, u}) (L : Cocone F)
    (hobjects : Nonempty (IsColimit (Cat.objects.mapCocone L)))
    (harrows : Nonempty (IsColimit (Cat.arrows.mapCocone L)))
    (D : Type v) [Category.{w} D] (v : ∀ j : J, F.obj j ⥤ D)
    (hcompat : ∀ (j k : J) (a : j ⟶ k), (F.map a).toFunctor ⋙ v k = v j) :
    ∃ V : L.pt ⥤ D, ∀ j : J, (L.ι.app j).toFunctor ⋙ V = v j := by
  sorry

end CategoryTheory
