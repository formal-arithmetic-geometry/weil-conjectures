/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.MetricSpace.PiNat

/-!
# Compact diagonal images of countably many finite coordinates

Source: the blueprint, `sec-six-functors-basics`,
`sk-thm-sf-ctf-stability-direct-images`, paragraph (3), auxiliary scalar tame-kernel
construction (blueprint: lem-sfb-countable-finite-coordinate-images).
The topological auxiliary argument is agent-formulated; the blueprint motivates its use.
Stacks Project, Topology, Tags 004E, 08ZS, 04Z9 and 0B1Z supply the topological definitions
and compact-image lemma. An external reference for the complete auxiliary lemma is wanted.
-/

@[expose] public section

set_option autoImplicit false

universe uS uG uA uB

open Topology

namespace Topology

/-- Countable finite-coordinate images are metrizable profinite spaces and groups.

Source: the blueprint, `sk-thm-sf-ctf-stability-direct-images`, paragraph (3), scalar
tame-kernel auxiliary construction; Stacks, Topology, Tags 004E, 08ZS, 04Z9 and 0B1Z.
(blueprint: lem-sfb-countable-finite-coordinate-images)

The space image is the subtype `Set.range (fun s n ↦ p n s)`. The group image is the
subgroup `(MonoidHom.pi q).range`, with its coordinatewise group structure and the same
subtype topology. Their corestrictions are `Set.rangeFactorization` and `rangeRestrict`.
For finite `F`, pulling back `Subgroup.pi F (fun n ↦ ⊥)` along the range inclusion gives
exactly the subgroup of image tuples whose coordinates in `F` equal the identity.

Proof plan (agent-formulated, following the node's seven steps):
1. Basic product opens constrain only finitely many coordinates. Their inverse images
   are finite intersections of open coordinate inverse images, proving continuity of
   the diagonal maps. The induced subtype topology proves continuity of both
   corestrictions; membership in the image proves their surjectivity.
2. Apply `isCompact_range` (lem-weil-pbc-continuous-image-quasi-compact, Stacks 04Z9)
   to both continuous diagonal maps to obtain compactness of their image subspaces.
3. Cylinders prescribing finitely many coordinate values are clopen in either image.
   Every neighbourhood contains such a cylinder. Different tuples differ in a
   coordinate, so these cylinders separate points and show total disconnectedness.
4. Give each finite discrete factor the metric taking values zero and one. Its
   triangle inequality follows since unequal endpoints force one adjacent pair to
   be unequal; radius-one-half balls are singletons. Image coordinate projections
   are continuous and separate points. Apply
   `Metric.PiNatEmbed.TopologicalSpace.MetrizableSpace.of_countable_separating`
   (lem-sfb-compact-countable-separating-metrizable) to each compact image.
5. Coordinate homomorphism identities make the group image a subgroup and its
   corestriction a homomorphism. Multiplication pulls a singleton coordinate cylinder
   back to the union of rectangles with coordinate products equal to its value;
   inversion pulls it back to the cylinder at the inverse value. These inverse
   images are open, proving continuity of both operations in the subtype topology.
6. The finite-coordinate identity cylinders are subgroups, open by step 3. They are
   normal because coordinate conjugation preserves the identity. Every identity
   neighbourhood contains such a cylinder, yielding the asserted filter basis.
   For the empty finite set the subgroup is the whole image.
7. Subtype equality is tuple equality, which is coordinatewise equality. Empty `S`
   gives an empty image; an empty `A n` forces `S` empty whenever `p n` exists.
   Groups contain the identity, so the group image is always nonempty. No coordinate
   surjectivity, completeness or nonemptiness of the space factors was used.
   The four explicit universe levels implement def-weil-size-convention. -/
theorem countable_finite_coordinate_images
    (S : Type uS) [TopologicalSpace S] [CompactSpace S] [T2Space S]
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G]
    (A : ℕ → Type uA) [∀ n, Finite (A n)] [∀ n, TopologicalSpace (A n)]
    [∀ n, DiscreteTopology (A n)]
    (B : ℕ → Type uB) [∀ n, Group (B n)] [∀ n, Finite (B n)]
    [∀ n, TopologicalSpace (B n)] [∀ n, DiscreteTopology (B n)]
    (p : ∀ n, S → A n) (hp : ∀ n, Continuous (p n))
    (q : ∀ n, G →* B n) (hq : ∀ n, Continuous (q n)) :
    Continuous (Set.rangeFactorization (fun s n ↦ p n s)) ∧
    Function.Surjective (Set.rangeFactorization (fun s n ↦ p n s)) ∧
    CompactSpace (Set.range (fun s n ↦ p n s)) ∧
    T2Space (Set.range (fun s n ↦ p n s)) ∧
    TopologicalSpace.IsTopologicalBasis
      {U : Set (Set.range (fun s n ↦ p n s)) | IsClopen U} ∧
    TopologicalSpace.MetrizableSpace (Set.range (fun s n ↦ p n s)) ∧
    TotallyDisconnectedSpace (Set.range (fun s n ↦ p n s)) ∧
    Continuous (MonoidHom.pi q).rangeRestrict ∧
    Function.Surjective (MonoidHom.pi q).rangeRestrict ∧
    IsTopologicalGroup (MonoidHom.pi q).range ∧
    CompactSpace (MonoidHom.pi q).range ∧
    T2Space (MonoidHom.pi q).range ∧
    TopologicalSpace.MetrizableSpace (MonoidHom.pi q).range ∧
    TotallyDisconnectedSpace (MonoidHom.pi q).range ∧
    (∀ F : Finset ℕ,
      IsOpen ((Subgroup.pi (F : Set ℕ) (fun n ↦ (⊥ : Subgroup (B n)))).comap
        (MonoidHom.pi q).range.subtype : Set (MonoidHom.pi q).range) ∧
      ((Subgroup.pi (F : Set ℕ) (fun n ↦ (⊥ : Subgroup (B n)))).comap
        (MonoidHom.pi q).range.subtype).Normal) ∧
    (𝓝 (1 : (MonoidHom.pi q).range)).HasBasis (fun _ : Finset ℕ ↦ True)
      (fun F ↦ ((Subgroup.pi (F : Set ℕ) (fun n ↦ (⊥ : Subgroup (B n)))).comap
        (MonoidHom.pi q).range.subtype : Set (MonoidHom.pi q).range)) ∧
    (∀ s s' : S,
      Set.rangeFactorization (fun s n ↦ p n s) s =
        Set.rangeFactorization (fun s n ↦ p n s) s' ↔ ∀ n, p n s = p n s') ∧
    (∀ g g' : G,
      (MonoidHom.pi q).rangeRestrict g = (MonoidHom.pi q).rangeRestrict g' ↔
        ∀ n, q n g = q n g') := by
  sorry

end Topology
