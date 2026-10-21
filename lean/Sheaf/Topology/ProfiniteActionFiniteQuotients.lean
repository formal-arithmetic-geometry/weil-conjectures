module

public import Sheaf.Topology.InvariantDiscreteQuotient
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.Compactness.Compact

/-! # Finite equivariant quotient presentations of profinite actions

Source: Bhatt–Scholze, The pro-étale topology for schemes, Example 4.1.10, p. 28;
Stacks Project, Tags 08ZY, 08ZU, 08ZV and 0A2P.
(blueprint: lem-sfb-profinite-action-finite-quotients)

All spaces and index sets use explicit universes, implementing the metatheoretic
size convention def-weil-size-convention. The concrete Mathlib limit cone is the
subspace of compatible families in the product, with its product/subspace topology.
Actions and the homeomorphism below are pinned down by their values on projections.
-/

@[expose] public section

universe u v

open CategoryTheory Topology

/-- Every profinite continuous action is the inverse limit of its finite invariant
clopen quotients, and compatible-family limits of finite continuous actions are
profinite continuous actions, including empty spaces and empty stages.

Source: Bhatt–Scholze, Example 4.1.10, p. 28; Stacks, Tags 08ZY, 08ZU, 08ZV, 0A2P.
(blueprint: lem-sfb-profinite-action-finite-quotients)

Proof plan:
1. For a finite clopen partition, continuity near (1,x) gives neighbourhoods V_x,W_x
   with V_x W_x inside the block of x. A finite W_x cover gives a neighbourhood V
   preserving every block. Choose an open normal subgroup N inside V. Inverses
   show that N fixes each block setwise. The empty space is handled separately.
2. Compactness of G supplies a finite coset cover modulo N, hence finitely many
   translated partitions. Their common refinement is finite, invariant and finer
   than the given partition.
3. The invariant quotient index is small, has a trivial quotient and common
   refinements. Containing-block maps compose and are surjective by choosing a
   point of each coarse block; projection maps are likewise surjective.
4. Define the quotient action by g.[x]=[gx]. It is continuous: for a block B choose
   x in B, and gB=C iff gx lies in C. Projections and transition maps are equivariant.
5. The clopen basis (lem-weil-pbc-profinite-clopen-basis) and invariant refinements
   separate points, proving injectivity of the canonical compatible-family map.
6. A compatible family of nonempty closed blocks has the finite intersection
   property, using common refinements. Compactness gives a point in all blocks,
   proving surjectivity. For empty P an empty coordinate forces an empty limit.
7. The map is continuous coordinatewise, and the target is Hausdorff. Apply
   lem-weil-pbc-compact-hausdorff-bijection to obtain the canonical homeomorphism;
   its equivariance follows coordinatewise.
8. For an arbitrary system, finite discrete stages are compact, so their product
   is compact by lem-weil-pbc-tychonoff-product-quasi-compact. Compatibility
   equations define a closed subspace. This proves compactness, even if empty.
9. Coordinate singleton cylinders separate points and separate any connected
   subset containing two distinct points. The limit is Hausdorff and totally
   disconnected, with no surjectivity assumption on the transitions.
10. Equivariance of transitions makes the coordinatewise action preserve the
    compatibility equations. Each action coordinate is continuous by joint
    continuity on its stage, hence the limit action is jointly continuous. -/
theorem profiniteAction_finite_quotients
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G]
    (hG : ∀ U ∈ 𝓝 (1 : G), ∃ N : OpenNormalSubgroup G, (N : Set G) ⊆ U) :
    (∀ (P : Type v) [TopologicalSpace P] [CompactSpace P] [T2Space P]
        [TotallyDisconnectedSpace P] [MulAction G P] [ContinuousSMul G P],
      (∀ s : DiscreteQuotient P, ∃ i : InvariantDiscreteQuotient G P, i.val ≤ s) ∧
      IsCofiltered (InvariantDiscreteQuotient G P) ∧
      (∀ i : InvariantDiscreteQuotient G P,
        Finite i.val ∧ DiscreteTopology i.val ∧ Function.Surjective i.val.proj) ∧
      (∀ (i j : InvariantDiscreteQuotient G P) (h : i ≤ j),
        Function.Surjective (DiscreteQuotient.ofLE h)) ∧
      ∃ (a : ∀ i : InvariantDiscreteQuotient G P, MulAction G i.val)
        (b : MulAction G (TopCat.limitCone (invariantDiscreteQuotientDiagram G P)).pt),
        (∀ i : InvariantDiscreteQuotient G P, ContinuousSMul G i.val) ∧
        (∀ (g : G) (p : P) (i : InvariantDiscreteQuotient G P),
          i.val.proj (g • p) = g • i.val.proj p) ∧
        (∀ (i j : InvariantDiscreteQuotient G P) (h : i ≤ j) (g : G) (x : i.val),
          DiscreteQuotient.ofLE h (g • x) = g • DiscreteQuotient.ofLE h x) ∧
        ContinuousSMul G (TopCat.limitCone (invariantDiscreteQuotientDiagram G P)).pt ∧
        (∀ (g : G) (z : (TopCat.limitCone (invariantDiscreteQuotientDiagram G P)).pt)
            (i : InvariantDiscreteQuotient G P),
          (g • z).val i = @SMul.smul G i.val (a i).toSMul g (z.val i)) ∧
        ∃ e : P ≃ₜ (TopCat.limitCone (invariantDiscreteQuotientDiagram G P)).pt,
          (∀ (p : P) (i : InvariantDiscreteQuotient G P), (e p).val i = i.val.proj p) ∧
          (∀ (g : G) (p : P), e (g • p) = g • e p)) ∧
    (∀ (I : Type v) [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]
        (F : Iᵒᵖ ⥤ TopCat.{v}) [∀ i : Iᵒᵖ, Finite (F.obj i)]
        [∀ i : Iᵒᵖ, DiscreteTopology (F.obj i)] [∀ i : Iᵒᵖ, MulAction G (F.obj i)]
        [∀ i : Iᵒᵖ, ContinuousSMul G (F.obj i)],
      (∀ (i j : Iᵒᵖ) (f : i ⟶ j) (g : G) (x : F.obj i),
        F.map f (g • x) = g • F.map f x) →
      CompactSpace (TopCat.limitCone F).pt ∧ T2Space (TopCat.limitCone F).pt ∧
      TotallyDisconnectedSpace (TopCat.limitCone F).pt ∧
      ∃ b : MulAction G (TopCat.limitCone F).pt,
        ContinuousSMul G (TopCat.limitCone F).pt ∧
        ∀ (g : G) (z : (TopCat.limitCone F).pt) (i : Iᵒᵖ),
          (g • z).val i = g • z.val i) := by
  sorry
