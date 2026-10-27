module

public import Mathlib.Topology.DiscreteQuotient
public import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Homeomorph.Lemmas

/-! # Reconstruction from cofinal finite clopen partitions

Source: Stacks Project, topology.tex, Tag 08ZY (lemma-profinite), proof of (2) implies (1),
restricted to a cofinal directed collection; Tags 005D and 08YE.
(blueprint: lem-sfb-cofinal-clopen-partition-reconstruction)

On a compact space, Mathlib's `DiscreteQuotient` is precisely a finite clopen partition:
its elements represent the nonempty blocks, with block projection `proj`. Its order is
opposite to the order in the source: `j ≤ i` means that `j` refines `i`.
-/

@[expose] public section

universe u

set_option autoImplicit false

namespace Topology

/-- The compatibility subspace of the product of the discrete block sets of a collection
of clopen partitions. On compact spaces every block set is finite. The subtype has the
subspace topology of the product; the containing-block maps are `DiscreteQuotient.ofLE`.
Source: Stacks Project, Tag 08ZY, lemma-profinite, partition-limit construction
(blueprint: lem-sfb-cofinal-clopen-partition-reconstruction). -/
abbrev cofinalClopenPartitionLimit {P : Type u} [TopologicalSpace P]
    (J : Set (DiscreteQuotient P)) :=
  {b : (i : J) → i.val // ∀ (i j : J) (hji : j.val ≤ i.val),
    DiscreteQuotient.ofLE hji (b j) = b i}

/-- The canonical map sends a point to its block in each partition. Compatibility is
Mathlib's `DiscreteQuotient.ofLE_proj`, so this construction has no postponed data or proofs.
Source: Stacks Project, Tag 08ZY, lemma-profinite, canonical map to the partition limit
(blueprint: lem-sfb-cofinal-clopen-partition-reconstruction). -/
def cofinalClopenPartitionMap {P : Type u} [TopologicalSpace P]
    (J : Set (DiscreteQuotient P)) (x : P) : cofinalClopenPartitionLimit J :=
  ⟨fun i ↦ i.val.proj x, fun _ _ hji ↦ DiscreteQuotient.ofLE_proj hji x⟩

/-- A compact Hausdorff totally disconnected space is reconstructed from any nonempty
cofinal directed collection of finite clopen partitions, including the empty-space case.

Source: Stacks Project, Tag 08ZY, lemma-profinite, proof of (2) implies (1), restricted to
such a collection; Tags 005D (finite intersections) and 08YE (compact Hausdorff bijection)
(blueprint: lem-sfb-cofinal-clopen-partition-reconstruction).

Proof to be supplied in stage 3:
1. If P is empty, every quotient block set is empty. Choose an index using nonemptiness
   of J. Evaluation at this index rules out a compatible tuple, so the limit is empty.
2. For distinct points, use lem-weil-pbc-profinite-clopen-basis to choose a clopen
   containing the first but not the second. Its two-block partition has a refinement
   in J by cofinality, and this refinement separates the two points.
3. The formula ofLE_proj gives compatibility of the canonical map. Each coordinate is
   continuous, hence the map into the product subspace is continuous. Distinct tuples
   differ at some coordinate, whose discrete topology separates them; the limit is T2.
4. For a compatible tuple, the selected blocks are nonempty closed subsets. Directedness
   gives a common refinement for every finite set of indices (start with a fixed index
   for the empty finite set). The selected block at that refinement lies in every
   selected block of the finite set. Apply lem-sfb-compact-closed-finite-intersection
   to obtain a point in the intersection of all selected blocks.
5. Its projections are the given tuple, proving surjectivity. Separation from step 2
   proves injectivity and uniqueness of the point in the block intersection.
6. Apply lem-weil-pbc-compact-hausdorff-bijection to the continuous bijection from the
   compact source to the Hausdorff limit. Its inverse sends a tuple to precisely the
   unique point of its block intersection, giving the stated singleton equality.
-/
theorem cofinal_clopen_partition_reconstruction
    (P : Type u) [TopologicalSpace P] [CompactSpace P] [T2Space P]
    [TotallyDisconnectedSpace P] (J : Set (DiscreteQuotient P))
    (hne : J.Nonempty)
    (hdir : ∀ i j : J, ∃ k : J, k.val ≤ i.val ∧ k.val ≤ j.val)
    (hcofinal : ∀ Q : DiscreteQuotient P, ∃ i : J, i.val ≤ Q) :
    T2Space (cofinalClopenPartitionLimit J) ∧
      (∀ x y : P, x ≠ y → ∃ i : J, i.val.proj x ≠ i.val.proj y) ∧
      (∃ e : P ≃ₜ cofinalClopenPartitionLimit J,
        (∀ x : P, e x = cofinalClopenPartitionMap J x) ∧
        ∀ b : cofinalClopenPartitionLimit J,
          (⋂ i : J, i.val.proj ⁻¹' {b.val i}) = {e.symm b}) ∧
      (IsEmpty P → IsEmpty (cofinalClopenPartitionLimit J)) := by
  classical
  have : Nonempty J := hne.to_subtype
  have hsep : ∀ x y : P, x ≠ y → ∃ i : J, i.val.proj x ≠ i.val.proj y := by
    intro x y hxy
    by_contra h
    apply hxy
    apply DiscreteQuotient.eq_of_forall_proj_eq
    intro Q
    obtain ⟨i, hi⟩ := hcofinal Q
    have heq : i.val.proj x = i.val.proj y := by
      by_contra hne
      exact h ⟨i, hne⟩
    simpa only [DiscreteQuotient.ofLE_proj] using
      congrArg (DiscreteQuotient.ofLE hi) heq
  have hinj : Function.Injective (cofinalClopenPartitionMap J) := by
    intro x y hxy
    by_contra hne
    obtain ⟨i, hi⟩ := hsep x y hne
    exact hi (congrArg (fun b : cofinalClopenPartitionLimit J ↦ b.val i) hxy)
  have hsurj : Function.Surjective (cofinalClopenPartitionMap J) := by
    intro b
    let C : J → Set P := fun i ↦ i.val.proj ⁻¹' {b.val i}
    have hclosed : ∀ i, IsClosed (C i) := fun i ↦ i.val.isClosed_preimage _
    have hsub : ∀ i j : J, j.val ≤ i.val → C j ⊆ C i := by
      intro i j hji x hx
      change i.val.proj x = b.val i
      change j.val.proj x = b.val j at hx
      rw [← DiscreteQuotient.ofLE_proj hji x, hx, b.property i j hji]
    have hdirC : Directed (· ⊇ ·) C := by
      intro i j
      obtain ⟨k, hki, hkj⟩ := hdir i j
      exact ⟨k, hsub i k hki, hsub j k hkj⟩
    obtain ⟨x, hx⟩ :=
      IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed C hdirC
        (fun i ↦ (Set.singleton_nonempty _).preimage i.val.proj_surjective)
        (fun i ↦ (hclosed i).isCompact) hclosed
    refine ⟨x, Subtype.ext (funext fun i ↦ ?_)⟩
    exact Set.mem_iInter.mp hx i
  have hcont : Continuous (cofinalClopenPartitionMap J) :=
    (continuous_pi fun i ↦ i.val.proj_continuous).subtype_mk _
  let e : P ≃ₜ cofinalClopenPartitionLimit J :=
    (isHomeomorph_iff_continuous_bijective.mpr ⟨hcont, hinj, hsurj⟩).homeomorph _
  refine ⟨inferInstance, hsep, ⟨e, fun _ ↦ rfl, ?_⟩, ?_⟩
  · intro b
    ext x
    simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hx
      apply e.injective
      exact (Subtype.ext (funext hx)).trans (e.apply_symm_apply b).symm
    · rintro rfl i
      exact congrArg (fun c : cofinalClopenPartitionLimit J ↦ c.val i)
        (e.apply_symm_apply b)
  · intro hempty
    exact ⟨fun b ↦ hempty.false (e.symm b)⟩

end Topology
