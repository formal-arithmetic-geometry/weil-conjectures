module

public import Mathlib.Data.PNat.Basic
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.Order
import Sheaf.Topology.ShrinkingClopenPartitions
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Topology.LocallyConstant.Basic

/-! # Finite clopen partitions and product retractions for a closed cover.

This is the partition, product embedding, and retraction portion of the
closed-cover selector construction.
Source: the parent node's scalar analytic expansion, steps 1--5.
(blueprint: lem-sfb-closed-cover-partitions-product)
-/

@[expose] public section

universe u

open Topology

namespace TopologicalSpace

private theorem partition_covers {S : Type u} (P : Finpartition (Set.univ : Set S))
    (s : S) : ∃ p ∈ P.parts, s ∈ p := by
  have h : s ∈ P.parts.sup id := P.sup_parts.symm ▸ Set.mem_univ s
  simpa only [Finset.sup_set_eq_biUnion, Set.mem_iUnion, id_eq, exists_prop] using h

private theorem partition_unique {S : Type u} (P : Finpartition (Set.univ : Set S))
    {p q : Set S} (hp : p ∈ P.parts) (hq : q ∈ P.parts) {s : S}
    (hsp : s ∈ p) (hsq : s ∈ q) : p = q := by
  by_contra hne
  exact Set.disjoint_left.mp (P.disjoint hp hq hne) hsp hsq

/-- The partition, product embedding, and closed-cover retraction data used by
`exists_closedCover_retractions_stabilizingSelectors`.

Proof: take shrinking finite clopen partitions and send each point to its unique
containing atom at every level. Coordinates are locally constant. The diameter
bounds make this map injective. A continuous injection from a compact space
into a Hausdorff product is a closed embedding, so the closed sets have closed
images. Reindex the coordinates by `n + 1`. Apply
`PiNat.exists_retraction_subtype_of_isClosed` to each nonempty closed image,
then compose with the inverse homeomorphism from that image to `A j`.
The retraction identity follows from the identity on the product image.
Source: scalar analytic expansion of paragraph (3), old steps 5--6, of
`sk-thm-sf-ctf-stability-direct-images.proof.md`.
(blueprint: lem-sfb-closed-cover-partitions-product)
-/
theorem exists_closedCover_partitions_product
    (S : Type u) [MetricSpace S] [CompactSpace S] [TotallyDisconnectedSpace S]
    [Nonempty S] (A : ℕ+ → Set S) (hclosed : ∀ j, IsClosed (A j))
    (hnonempty : ∀ j, (A j).Nonempty) :
    ∃ P : ℕ+ → Finpartition (Set.univ : Set S),
      (∀ i, P (i + 1) ≤ P i) ∧
      (∀ i p, p ∈ (P i).parts → IsClopen p ∧ Metric.diam p < (1 / 2 : ℝ) ^ (i : ℕ)) ∧
      ∃ ρ : ∀ j, C(S, A j),
        (∀ j (a : A j), ρ j a = a) ∧
        ∃ e : S → ∀ i : ℕ+, WithDiscreteTopology (P i).parts,
          (∀ s i, s ∈ (e s i).ofTopology.val) ∧ IsEmbedding e ∧
          (∀ j, (e '' A j).Nonempty ∧ IsClosed (e '' A j)) := by
  classical
  obtain ⟨P, hrefine, hatoms⟩ := exists_shrinking_clopen_partitions S
  let e : S → ∀ i : ℕ+, WithDiscreteTopology (P i).parts := fun s i ↦
    WithTopology.toTopology ⊥
      ⟨(partition_covers (P i) s).choose, (partition_covers (P i) s).choose_spec.1⟩
  have he (s : S) (i : ℕ+) : s ∈ (e s i).ofTopology.val :=
    (partition_covers (P i) s).choose_spec.2
  have hecont : Continuous e := by
    apply continuous_pi
    intro i
    apply IsLocallyConstant.continuous
    rw [IsLocallyConstant.iff_exists_open]
    intro s
    refine ⟨(e s i).ofTopology.val, (hatoms i _ (e s i).ofTopology.property).1.isOpen,
      he s i, ?_⟩
    intro t ht
    apply WithTopology.ext
    apply Subtype.ext
    exact partition_unique (P i) (e t i).ofTopology.property
      (e s i).ofTopology.property (he t i) ht
  have heinj : Function.Injective e := by
    intro s t hst
    by_contra hne
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (1 / 2 : ℝ) ^ n < dist s t :=
      exists_pow_lt_of_lt_one (dist_pos.mpr hne) (by norm_num)
    let i : ℕ+ := n.succPNat
    have hi : (1 / 2 : ℝ) ^ (i : ℕ) < dist s t :=
      lt_of_le_of_lt (pow_le_pow_of_le_one (by norm_num) (by norm_num)
        (show n ≤ (i : ℕ) from Nat.le_succ n)) hn
    have heq : (e s i).ofTopology.val = (e t i).ofTopology.val :=
      congrArg (fun f ↦ (f i).ofTopology.val) hst
    have htp : t ∈ (e s i).ofTopology.val := heq.symm ▸ he t i
    have hd := Metric.dist_le_diam_of_mem
      (isCompact_univ.isBounded.subset (Set.subset_univ _)) (he s i) htp
    exact (not_lt_of_ge hd) ((hatoms i _ (e s i).ofTopology.property).2.trans hi)
  have hemb : IsEmbedding e := (hecont.isClosedEmbedding heinj).isEmbedding
  have himage (j : ℕ+) : (e '' A j).Nonempty ∧ IsClosed (e '' A j) :=
    ⟨(hnonempty j).image e, hecont.isClosedMap _ (hclosed j)⟩
  let en : S → ∀ n : ℕ, WithDiscreteTopology (P n.succPNat).parts :=
    fun s n ↦ e s n.succPNat
  have hencont : Continuous en :=
    continuous_pi fun n ↦ (continuous_apply n.succPNat).comp hecont
  have heninj : Function.Injective en := by
    intro s t h
    apply heinj
    funext i
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, n.succPNat = i :=
      ⟨i.natPred, PNat.succPNat_natPred i⟩
    exact congrFun h n
  have henemb : IsEmbedding en := (hencont.isClosedEmbedding heninj).isEmbedding
  have hretract (j : ℕ+) : ∃ r : C(S, A j), ∀ a : A j, r a = a := by
    obtain ⟨r, hrfix, _, hrcont⟩ := PiNat.exists_retraction_subtype_of_isClosed
      (hencont.isClosedMap _ (hclosed j)) ((hnonempty j).image en)
    let H : A j ≃ₜ en '' A j := henemb.homeomorphImage (A j)
    refine ⟨⟨fun s ↦ H.symm (r (en s)), H.symm.continuous.comp (hrcont.comp hencont)⟩, ?_⟩
    intro a
    apply H.injective
    change H (H.symm (r (en a))) = H a
    rw [H.apply_symm_apply]
    have hHa : (H a).val = en a := rfl
    simpa only [hHa] using hrfix (H a)
  choose ρ hρ using hretract
  exact ⟨P, hrefine, hatoms, ρ, hρ, e, he, hemb, himage⟩

end TopologicalSpace
