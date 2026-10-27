module

public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit

/-!
# Almost filtered colimits of sets preserve pullbacks and equalizers

Source: Stacks Project, Categories, Tag 002Y, with the hypotheses of Tag 002X expanded
(blueprint: lem-sfb-almost-filtered-set-colimits).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace CategoryTheory.Limits

/-- Source: Stacks Project, Categories, Tags 002X and 002Y
(blueprint: lem-sfb-almost-filtered-set-colimits).

No nonemptiness or connectedness of the small index category is assumed. Sets live in
`Type (max u v)`, a chosen universe containing the index. Pullbacks and equalizers in the
functor category are computed objectwise, so the two comparison morphisms are the canonical
maps from the colimits of the pointwise fibre products and equalizers.

Proof:
1. Apply [lem-sfb-almost-filtered-components] to the two arrow conditions. Partition the
objects into nonempty filtered full subcategories with no arrows between different parts.
The set of parts and each full subcategory are small. For the empty category there are no parts.
2. By [def-weil-pbc-category-colimit], cocones on a diagram are precisely families of cocones
on its parts. Thus its colimit is canonically the disjoint union of the component colimits.
Natural transformations preserve the tags of this disjoint union; this includes an empty union.
3. On each filtered part apply [lem-weil-pbc-filtered-colimits-commute-finite-limits] to the
finite cospan and parallel-pair diagrams. The resulting comparison bijections send a pair to
its two classes, and an equalizer element to its class.
4. In the fibre product of the two tagged unions, equality of the images in the middle
union forces the tags to agree. Consequently that fibre product is the disjoint union of
the component fibre products. Combining this with steps 2 and 3 gives exactly the canonical
pullback comparison, sending a representative pair to its two colimit classes.
5. The two maps on the tagged unions preserve tags, so their values on a tagged element
are equal exactly when the two values in that component agree. Their equalizer is therefore
the disjoint union of the component equalizers. Steps 2 and 3 give exactly the canonical
equalizer comparison, sending a representative to its class. Both constructions also work
for no parts: all the sets in these two comparisons are empty. -/
theorem almostFiltered_colim_pullback_equalizer_bijective
    (I : Type u) [SmallCategory I]
    (hspan : ∀ (w x y : I) (a : w ⟶ x) (b : w ⟶ y),
      ∃ (z : I) (c : x ⟶ z) (d : y ⟶ z), a ≫ c = b ≫ d)
    (hparallel : ∀ (x y : I) (a b : x ⟶ y),
      ∃ (z : I) (c : y ⟶ z), a ≫ c = b ≫ c) :
    (∀ (A B C : I ⥤ Type (max u v)) (f : A ⟶ B) (g : C ⟶ B),
      Function.Bijective (pullbackComparison (colim : (I ⥤ Type (max u v)) ⥤ _) f g)) ∧
    (∀ (A B : I ⥤ Type (max u v)) (f g : A ⟶ B),
      Function.Bijective (equalizerComparison f g (colim : (I ⥤ Type (max u v)) ⥤ _))) := by
  sorry

end CategoryTheory.Limits
