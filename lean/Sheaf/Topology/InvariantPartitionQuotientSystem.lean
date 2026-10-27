module

public import Sheaf.Topology.InvariantDiscreteQuotient
public import Mathlib.CategoryTheory.Filtered.Basic

/-! # The continuous finite system of invariant clopen partitions

Source: Bhatt–Scholze, The pro-étale topology for schemes, Example 4.1.10, p. 28,
expanded by the finite partition construction of Stacks Project, Tag 08ZY.
(blueprint: lem-sfb-invariant-partition-quotient-system)

`OrderDual (InvariantDiscreteQuotient G P)` is the node's index `J`: a larger
index is a finer partition. A quotient element represents its nonempty clopen
fiber under `proj`. This uses the existing invariant-quotient notion, including
the empty partition for an empty space. All indices and quotients live in `Type v`.
-/

@[expose] public section

universe u v

open CategoryTheory

/-- Invariant finite clopen partitions form a small directed system, with continuous
surjective equivariant quotient maps, canonical refinement maps, and continuous block actions.

Source: Bhatt–Scholze, Example 4.1.10, p. 28, expanded using Stacks, Tag 08ZY.
(blueprint: lem-sfb-invariant-partition-quotient-system)

Proof plan:
1. Invariant discrete quotients are relations on the small underlying set. Their
   classes are clopen. Compactness makes the disjoint nonempty class cover finite.
   Conversely a finite clopen partition gives its same-block equivalence relation.
   Preservation of the relation by g and its inverse is equivalent to permuting blocks.
2. The indiscrete quotient supplies an index, even when P is empty. Intersections
   of blocks, discarding empty intersections, give invariant common refinements.
3. Refinement is a partial order: mutual refinement identifies blocks using a point
   in each block. Common refinements give cones in the opposite index category;
   parallel arrows are equal since the category comes from a partial order.
4. Quotient projections are continuous because inverse images are unions of open
   blocks. Choosing a point in any block proves surjectivity, vacuously for empty P.
5. A fine block has a unique containing coarse block. Choosing a point in a coarse
   block proves refinement maps surjective. Discreteness gives continuity, and
   uniqueness of containing blocks gives identities, composition, and compatibility.
6. Define g.[x] = [gx], well-defined by invariance. Images of blocks give this action.
   The group laws descend from P. Distinct blocks are disjoint, so gB=C exactly when
   gx lies in C for any chosen x in B.
7. The block containing gx is g times the block containing x. Images preserve
   containment, proving equivariance of projection and refinement maps.
8. For fixed blocks B,C choose x in B. The set of g with gx in C is open by joint
   continuity on P. The preimage of C under the block action is the union of these
   open sets times the open singleton B. This proves joint continuity, also for
   empty P, when the action domain is empty. -/
theorem invariantPartition_quotient_system
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (P : Type v) [TopologicalSpace P] [CompactSpace P]
    [MulAction G P] [ContinuousSMul G P] :
    Small.{v} (OrderDual (InvariantDiscreteQuotient G P)) ∧
    Nonempty (OrderDual (InvariantDiscreteQuotient G P)) ∧
    IsDirected (OrderDual (InvariantDiscreteQuotient G P)) (· ≤ ·) ∧
    IsCofiltered (OrderDual (InvariantDiscreteQuotient G P))ᵒᵖ ∧
    (∀ i : OrderDual (InvariantDiscreteQuotient G P),
      Finite i.val ∧ DiscreteTopology i.val ∧
      Continuous i.val.proj ∧ Function.Surjective i.val.proj) ∧
    (∀ (i j : OrderDual (InvariantDiscreteQuotient G P)) (h : i ≤ j),
      Continuous (DiscreteQuotient.ofLE h) ∧
      Function.Surjective (DiscreteQuotient.ofLE h)) ∧
    (∀ i : OrderDual (InvariantDiscreteQuotient G P),
      DiscreteQuotient.ofLE (le_refl i.val) = id) ∧
    (∀ (i j k : OrderDual (InvariantDiscreteQuotient G P)) (hij : i ≤ j) (hjk : j ≤ k),
      DiscreteQuotient.ofLE (le_trans hjk hij) =
        DiscreteQuotient.ofLE hij ∘ DiscreteQuotient.ofLE hjk) ∧
    (∀ (i j : OrderDual (InvariantDiscreteQuotient G P)) (h : i ≤ j),
      DiscreteQuotient.ofLE h ∘ j.val.proj = i.val.proj) ∧
    ∃ a : ∀ i : OrderDual (InvariantDiscreteQuotient G P), MulAction G i.val,
      (∀ i : OrderDual (InvariantDiscreteQuotient G P),
        @ContinuousSMul G i.val (a i).toSMul _ _) ∧
      (∀ (i : OrderDual (InvariantDiscreteQuotient G P)) (g : G) (B : i.val),
        i.val.proj ⁻¹' {@SMul.smul G i.val (a i).toSMul g B} =
          (fun x : P ↦ g • x) '' (i.val.proj ⁻¹' {B})) ∧
      (∀ (i : OrderDual (InvariantDiscreteQuotient G P)) (g : G) (x : P),
        i.val.proj (g • x) = @SMul.smul G i.val (a i).toSMul g (i.val.proj x)) ∧
      (∀ (i j : OrderDual (InvariantDiscreteQuotient G P)) (h : i ≤ j)
          (g : G) (B : j.val),
        DiscreteQuotient.ofLE h (@SMul.smul G j.val (a j).toSMul g B) =
          @SMul.smul G i.val (a i).toSMul g (DiscreteQuotient.ofLE h B)) ∧
      (∀ (i : OrderDual (InvariantDiscreteQuotient G P)) (g : G)
          (B C : i.val) (x : P),
        i.val.proj x = B →
          (@SMul.smul G i.val (a i).toSMul g B = C ↔ i.val.proj (g • x) = C)) := by
  let J := OrderDual (InvariantDiscreteQuotient G P)
  have hnonempty : Nonempty J := ⟨⟨⊤, fun _ _ _ _ ↦ trivial⟩⟩
  have hdirected : IsDirected J (· ≤ ·) := ⟨fun i j ↦ by
    refine ⟨⟨i.val ⊓ j.val, ?_⟩, ?_, ?_⟩
    · intro g x y h
      exact ⟨i.property g x y h.1, j.property g x y h.2⟩
    · change i.val ⊓ j.val ≤ i.val
      exact inf_le_left
    · change i.val ⊓ j.val ≤ j.val
      exact inf_le_right⟩
  have : Nonempty J := hnonempty
  have : IsDirected J (· ≤ ·) := hdirected
  let a (i : J) : MulAction G i.val :=
    { smul := fun g ↦ Quotient.map' (fun x : P ↦ g • x) (i.property g)
      one_smul := fun B ↦ by
        obtain ⟨x, rfl⟩ := i.val.proj_surjective B
        exact congrArg i.val.proj (one_smul G x)
      mul_smul := fun g h B ↦ by
        obtain ⟨x, rfl⟩ := i.val.proj_surjective B
        exact congrArg i.val.proj (mul_smul g h x) }
  have hproj (i : J) (g : G) (x : P) :
      i.val.proj (g • x) = @SMul.smul G i.val (a i).toSMul g (i.val.proj x) := rfl
  refine ⟨inferInstance, hnonempty, hdirected, inferInstance, ?_, ?_, ?_, ?_, ?_,
    a, ?_, ?_, hproj, ?_, ?_⟩
  · intro i
    exact ⟨inferInstance, inferInstance, i.val.proj_continuous, i.val.proj_surjective⟩
  · intro i j h
    refine ⟨DiscreteQuotient.ofLE_continuous h, ?_⟩
    intro B
    obtain ⟨x, rfl⟩ := i.val.proj_surjective B
    exact ⟨j.val.proj x, DiscreteQuotient.ofLE_proj h x⟩
  · intro i
    exact DiscreteQuotient.ofLE_refl
  · intro i j k hij hjk
    exact (DiscreteQuotient.ofLE_comp_ofLE hjk hij).symm
  · intro i j h
    exact DiscreteQuotient.ofLE_comp_proj h
  · intro i
    refine ⟨continuous_prod_of_discrete_right.mpr ?_⟩
    intro B
    obtain ⟨x, rfl⟩ := i.val.proj_surjective B
    exact i.val.proj_continuous.comp (continuous_id.smul continuous_const)
  · intro i g B
    let : MulAction G i.val := a i
    ext x
    change i.val.proj x = @SMul.smul G i.val (a i).toSMul g B ↔
      ∃ y, i.val.proj y = B ∧ g • y = x
    constructor
    · intro hx
      refine ⟨g⁻¹ • x, ?_, smul_inv_smul g x⟩
      rw [hproj, hx]
      exact inv_smul_smul g B
    · rintro ⟨y, hy, rfl⟩
      rw [hproj, hy]
  · intro i j h g B
    obtain ⟨x, rfl⟩ := j.val.proj_surjective B
    exact DiscreteQuotient.ofLE_proj h (g • x)
  · intro i g B C x hx
    rw [← hx, ← hproj]
