module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Filtered components from span and parallel-pair conditions

Source: Stacks Project, Categories, Tag 002X, `lemma-split-into-directed`
(blueprint: lem-sfb-almost-filtered-components).
-/

@[expose] public section

universe u

namespace CategoryTheory

/-- A small category satisfying the commuting-span and parallel-pair coequalization
conditions partitions into nonempty filtered full subcategories. Unique membership
expresses the partition, and the last clause excludes arrows between distinct parts.
There is no nonemptiness assumption on the ambient category or on the index set.

Source: Stacks Project, Categories, Tag 002X, `lemma-split-into-directed`
(blueprint: lem-sfb-almost-filtered-components).

Proof:
1. Relate two objects when they have arrows to a common target. Identities give
   reflexivity and exchanging the arrows gives symmetry.
2. For transitivity, apply the commuting-span hypothesis to the two arrows out of
   the shared middle object. Composing gives a common target for the outer objects.
3. Take the small quotient of the object set by this equivalence relation, with
   its equivalence classes as the subsets. These are nonempty and partition the
   objects. For an empty category the quotient is empty. Use the explicit universe
   convention of [def-weil-size-convention].
4. Every arrow relates its endpoints, using itself and the target's identity.
   Thus no arrow joins different classes.
5. Two objects in one class have a common target, which remains in that class by
   the preceding observation. Fullness puts both arrows in the full subcategory.
6. The parallel-pair hypothesis coequalizes any two arrows in a class. Its target
   remains in that class, again by step 4. Together with nonemptiness and step 5,
   these are exactly the three filteredness conditions of
   [def-weil-pbc-category-colimit], rendered by Mathlib's `IsFiltered`. -/
theorem exists_filtered_partition_of_span_coequalization
    (I : Type u) [SmallCategory I]
    (hspan : ∀ {w x y : I} (a : w ⟶ x) (b : w ⟶ y),
      ∃ (z : I) (c : x ⟶ z) (d : y ⟶ z), a ≫ c = b ≫ d)
    (hparallel : ∀ {x y : I} (a b : x ⟶ y),
      ∃ (z : I) (c : y ⟶ z), a ≫ c = b ≫ c) :
    ∃ (J : Type u) (S : J → Set I),
      (∀ x : I, ∃! j : J, x ∈ S j) ∧
      (∀ j : J, IsFiltered (ObjectProperty.FullSubcategory (fun x : I ↦ x ∈ S j))) ∧
      (∀ (j k : J) (x y : I), x ∈ S j → y ∈ S k → (x ⟶ y) → j = k) := by
  sorry

end CategoryTheory
