module

public import Sheaf.CategoryTheory.StrictDiagramPseudococone
public import WeilConjectures.CategoryTheory.ArrowsFunctor
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.EssentialImage

/-! # Effectivity of filtered pseudococones

Source: Stacks Project, Categories, Tag 04AX, finite-representative extension.
(blueprint: lem-per-filtered-pseudococone-effectivity)
-/

@[expose] public section

universe z u v

namespace CategoryTheory

open Limits

/-- Every coherent pseudococone is isomorphic to the restriction of a functor.

Source: Stacks Project, Categories, Tag 04AX, finite-representative extension, Steps 1--2
of lem-per-filtered-category-pseudococones.
(blueprint: lem-per-filtered-pseudococone-effectivity)

Proof: choose an object representative r_z for each colimit object z using the object
set-colimit hypothesis. For a pseudococone P put F(z) = P(r_z). Represent an arrow by
f:x→y at a stage and send it to T(r_source,x) followed by P(f) and T(y,r_target).
Here T is the canonical representative transport of
lem-per-filtered-pseudocone-representative-transport. Its complete-arrow naturality
and cocycle identity show independence of representatives. Lift a composable pair
and its endpoint identifications to one stage. The two middle transports cancel;
stage functoriality proves composition. The unit identity for T proves identities.
The transports from r_(v_i x) to (i,x) define the stage isomorphisms F v_i ≅ P_i.
Complete-arrow naturality makes them natural in x. The transition formula for T
makes them compatible with P's comparisons. Their inverses satisfy the inverse
modification equations by cancelling the invertible comparison components, so these
isomorphisms assemble to an isomorphism of pseudococones. -/
theorem filteredPseudococone_effective
    {J : Type z} [SmallCategory J] [IsFiltered J] (D : J ⥤ Cat.{z, z})
    (c : Cocone D) (hobjects : IsColimit (Cat.objects.mapCocone c))
    (harrows : IsColimit (Cat.arrows.mapCocone c))
    (A : Type u) [Category.{v} A] :
    (StrictDiagramPseudococone.restriction c A).EssSurj := by
  sorry

end CategoryTheory
