
module

public import Mathlib.Topology.Separation.Profinite
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.DiscreteQuotient

/-!
# Finite quotient fibre products of profinite spaces

Source: literature/stacks-project/topology.tex, Tags 08ZY and 0A2P; the compatible-partition
construction in literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
sk-def-sfb-pullback-from-point/lem-sfb-profinite-to-proetale-finite-limits.proof.md
(blueprint: lem-sfb-finite-quotient-fiber-product).
-/


universe u

@[expose] public section

set_option autoImplicit false

open Function Set TopologicalSpace

namespace Topology

/-- A compatible triple of finite clopen partitions for a span. On compact spaces,
`DiscreteQuotient` has finite carrier; its projection fibers are exactly the nonempty
clopen blocks, including the empty family when the space is empty.
Source: Stacks Project, Topology, Tag 08ZY (blueprint: lem-sfb-finite-quotient-fiber-product). -/
structure CompatibleFinitePartitionSpan {S₁ S S₂ : Type u}
    [TopologicalSpace S₁] [TopologicalSpace S] [TopologicalSpace S₂]
    (f₁ : C(S₁, S)) (f₂ : C(S₂, S)) where
  left : DiscreteQuotient S₁
  middle : DiscreteQuotient S
  right : DiscreteQuotient S₂
  leftCompatible : DiscreteQuotient.LEComap f₁ left middle
  rightCompatible : DiscreteQuotient.LEComap f₂ right middle

/-- Refinement of compatible triples (the later triple is finer). Mathlib orders discrete
quotients in the opposite direction to the index order of Stacks Tag 08ZY.
Source: Stacks Project, Topology, Tag 08ZY (blueprint: lem-sfb-finite-quotient-fiber-product). -/
def compatiblePartitionRefines {S₁ S S₂ : Type u}
    [TopologicalSpace S₁] [TopologicalSpace S] [TopologicalSpace S₂]
    {f₁ : C(S₁, S)} {f₂ : C(S₂, S)}
    (i j : CompatibleFinitePartitionSpan f₁ f₂) : Prop :=
  j.left ≤ i.left ∧ j.middle ≤ i.middle ∧ j.right ≤ i.right

/-- The finite pullback of the block sets at one compatible partition.
Source: Stacks Project, Topology, Tag 08ZY (blueprint: lem-sfb-finite-quotient-fiber-product). -/
abbrev finitePartitionFiber {S₁ S S₂ : Type u}
    [TopologicalSpace S₁] [TopologicalSpace S] [TopologicalSpace S₂]
    {f₁ : C(S₁, S)} {f₂ : C(S₂, S)}
    (i : CompatibleFinitePartitionSpan f₁ f₂) :=
  {x : i.left × i.right //
    DiscreteQuotient.map f₁ i.leftCompatible x.1 =
      DiscreteQuotient.map f₂ i.rightCompatible x.2}

/-- The topological pullback of a span.
Source: Stacks Project, Topology, Tag 08ZY (blueprint: lem-sfb-finite-quotient-fiber-product). -/
abbrev topologicalFiber {S₁ S S₂ : Type u}
    [TopologicalSpace S₁] [TopologicalSpace S] [TopologicalSpace S₂]
    (f₁ : C(S₁, S)) (f₂ : C(S₂, S)) :=
  {p : S₁ × S₂ // f₁ p.1 = f₂ p.2}

/-- The compatibility subspace of the product of the finite pullbacks.
Source: Stacks Project, Topology, Tag 0A2P (blueprint: lem-sfb-finite-quotient-fiber-product). -/
abbrev finitePartitionLimit {S₁ S S₂ : Type u}
    [TopologicalSpace S₁] [TopologicalSpace S] [TopologicalSpace S₂]
    {f₁ : C(S₁, S)} {f₂ : C(S₂, S)}
    (b : ∀ (i j : CompatibleFinitePartitionSpan f₁ f₂),
      compatiblePartitionRefines i j → finitePartitionFiber j → finitePartitionFiber i) :=
  {x : ∀ i : CompatibleFinitePartitionSpan f₁ f₂, finitePartitionFiber i //
    ∀ (i j : CompatibleFinitePartitionSpan f₁ f₂)
      (hij : compatiblePartitionRefines i j), b i j hij (x j) = x i}

/-- The profinite span is the inverse limit of the compatible finite pullbacks.

Source: Stacks Project, Topology, Tags 08ZY (lemma-profinite), 0A2P (lemma-describe-limits),
and 08YE (compact-to-Hausdorff bijection), with the compatible-partition construction in the
blueprint proof (blueprint: lem-sfb-finite-quotient-fiber-product).

Proof, to be supplied in stage 3: the equalizer in the product is closed, hence compact
Hausdorff and totally disconnected. Intersecting finite clopen partitions gives a common
refinement. Trivial partitions give a compatible triple, including empty spaces, so this is
a nonempty directed system. Refinement induces maps of the finite pullbacks. Clopen separation
(using `lem-weil-pbc-profinite-clopen-basis`) and the finite-intersection property give a
bijection with the compatibility subspace. More explicitly, every source partition occurs
in a triple with trivial middle partition. For a coherent family the chosen blocks in each
source have the finite intersection property by common refinement. Compactness gives a point
in each source; clopen separation makes it unique. Every middle partition occurs with its
two inverse images, so the images of the two points lie in the same block of every middle
partition and are equal by clopen separation. Conversely separating a differing coordinate
shows injectivity. The refinement maps commute with the middle-block maps because they are
induced by the same continuous span maps. Finally its coordinate maps are continuous, and the
bijection is a homeomorphism because the source is compact and the target is Hausdorff.
The empty-space cases use the empty partition and produce the empty pullback and empty limit.
The size convention is the metatheoretic universe convention of `def-weil-size-convention`.
-/
theorem finite_quotient_fiber_product
    (S₁ S S₂ : Type u)
    [TopologicalSpace S₁] [TopologicalSpace S] [TopologicalSpace S₂]
    [CompactSpace S₁] [CompactSpace S] [CompactSpace S₂]
    [T2Space S₁] [T2Space S] [T2Space S₂]
    [TotallyDisconnectedSpace S₁] [TotallyDisconnectedSpace S]
    [TotallyDisconnectedSpace S₂]
    (f₁ : C(S₁, S)) (f₂ : C(S₂, S)) :
    CompactSpace (topologicalFiber f₁ f₂) ∧
      T2Space (topologicalFiber f₁ f₂) ∧
      TotallyDisconnectedSpace (topologicalFiber f₁ f₂) ∧
      Nonempty (CompatibleFinitePartitionSpan f₁ f₂) ∧
      (∀ i j : CompatibleFinitePartitionSpan f₁ f₂,
        ∃ k : CompatibleFinitePartitionSpan f₁ f₂,
          compatiblePartitionRefines i k ∧ compatiblePartitionRefines j k) ∧
      ∃ (p : ∀ i : CompatibleFinitePartitionSpan f₁ f₂,
          topologicalFiber f₁ f₂ → finitePartitionFiber i),
        (∀ (i : CompatibleFinitePartitionSpan f₁ f₂) (q : topologicalFiber f₁ f₂),
          (p i q).1.1 = i.left.proj q.1.1 ∧
            (p i q).1.2 = i.right.proj q.1.2) ∧
        (∀ i, Continuous (p i)) ∧
        ∃ (b : ∀ (i j : CompatibleFinitePartitionSpan f₁ f₂),
            compatiblePartitionRefines i j → finitePartitionFiber j → finitePartitionFiber i),
          (∀ (i j : CompatibleFinitePartitionSpan f₁ f₂)
              (hij : compatiblePartitionRefines i j) (x : finitePartitionFiber j),
            (b i j hij x).1.1 = DiscreteQuotient.ofLE hij.1 x.1.1 ∧
              (b i j hij x).1.2 = DiscreteQuotient.ofLE hij.2.2 x.1.2) ∧
          (∀ (i j k : CompatibleFinitePartitionSpan f₁ f₂)
              (hij : compatiblePartitionRefines i j)
              (hjk : compatiblePartitionRefines j k)
              (hik : compatiblePartitionRefines i k)
              (x : finitePartitionFiber k),
            b i k hik x = b i j hij (b j k hjk x)) ∧
          ∃ (coh : ∀ (q : topologicalFiber f₁ f₂)
              (i j : CompatibleFinitePartitionSpan f₁ f₂)
              (hij : compatiblePartitionRefines i j),
              b i j hij (p j q) = p i q),
            ∃ (h : topologicalFiber f₁ f₂ ≃ₜ finitePartitionLimit b),
              ∀ (q : topologicalFiber f₁ f₂),
                h q = ⟨fun i => p i q, coh q⟩ := by
  sorry

end Topology

end
