module

public import Mathlib.Topology.DiscreteQuotient
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.CategoryTheory.Category.Preorder

/-! # The diagram of invariant clopen quotient partitions

Source: Bhatt–Scholze, The pro-étale topology for schemes, Example 4.1.10, p. 28;
Stacks Project, Tag 08ZY, clopen quotient partitions.
(blueprint: def-sfb-invariant-discrete-quotients)

The order is Mathlib's refinement order: a finer partition is smaller. Thus the
index category itself is cofiltered, without taking its opposite. On a compact
space every discrete quotient is finite. Quotient classes are the nonempty
blocks, so the empty space has its empty partition.
-/

@[expose] public section

universe u v

open CategoryTheory

/-- The discrete quotients whose equivalence relations are preserved by the action.
For a group, preservation also by inverses says exactly that the group permutes
blocks, rather than fixing each block. Compactness makes these partitions finite.
Source: Bhatt–Scholze, Example 4.1.10, p. 28; Stacks, Tag 08ZY.
(blueprint: def-sfb-invariant-discrete-quotients) -/
abbrev InvariantDiscreteQuotient (G : Type u) [Group G] (P : Type v)
    [TopologicalSpace P] [MulAction G P] : Type v :=
  {s : DiscreteQuotient P // ∀ (g : G) (x y : P),
    s.toSetoid x y → s.toSetoid (g • x) (g • y)}

/-- The canonical quotient diagram: objects are blocks and maps send a fine block
to its containing coarse block. The topology on each quotient is discrete.
Source: Bhatt–Scholze, Example 4.1.10, p. 28; Stacks, Tag 08ZY.
(blueprint: def-sfb-invariant-discrete-quotients) -/
def invariantDiscreteQuotientDiagram (G : Type u) [Group G] (P : Type v)
    [TopologicalSpace P] [MulAction G P] : InvariantDiscreteQuotient G P ⥤ TopCat.{v} where
  obj i := TopCat.of i.val
  map f := TopCat.ofHom
    ⟨DiscreteQuotient.ofLE f.le, DiscreteQuotient.ofLE_continuous f.le⟩
  map_id i := by
    ext x
    exact DiscreteQuotient.ofLE_refl_apply x
  map_comp f g := by
    ext x
    exact (DiscreteQuotient.ofLE_ofLE f.le g.le x).symm
