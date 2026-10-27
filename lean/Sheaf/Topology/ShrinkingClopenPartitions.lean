module

public import Mathlib.Data.PNat.Basic
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Separation.DisjointCover

/-! # Shrinking refining finite clopen partitions of a compact totally disconnected metric space.
Source: Stacks Project, Topology, tag 08ZZ, and parent construction step 1.
(blueprint: lem-sfb-shrinking-clopen-partitions)
-/

@[expose] public section

universe u

open Topology

namespace TopologicalSpace

private theorem exists_small_clopen_partition
    (S : Type u) [MetricSpace S] [CompactSpace S] [TotallyDisconnectedSpace S]
    (ε : ℝ) (hε : 0 < ε) :
    ∃ P : Finpartition (Set.univ : Set S),
      ∀ p ∈ P.parts, IsClopen p ∧ Metric.diam p < ε := by
  classical
  let U : S → Opens S := fun s ↦ ⟨Metric.ball s (ε / 3), Metric.isOpen_ball⟩
  have hU : IsOpenCover U := by
    apply IsOpenCover.of_sets
    apply Set.eq_univ_of_forall
    intro s
    exact Set.mem_iUnion.mpr ⟨s, Metric.mem_ball_self (by linarith)⟩
  obtain ⟨n, W, hW, hcover, hdisjoint⟩ := hU.exists_finite_nonempty_disjoint_clopen_cover
  let F : Finset (Set S) := Finset.univ.image fun i ↦ (W i : Set S)
  have hF (p : Set S) : p ∈ F ↔ ∃ i, (W i : Set S) = p := by simp [F]
  have hsup : F.sup id = (Set.univ : Set S) := by
    apply Set.eq_univ_of_forall
    intro s
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover (Set.mem_univ s))
    simp only [Finset.sup_set_eq_biUnion, Set.mem_iUnion, id_eq]
    exact ⟨W i, (hF _).mpr ⟨i, rfl⟩, hi⟩
  let P : Finpartition (Set.univ : Set S) :=
    { parts := F
      supIndep := Finset.supIndep_iff_pairwiseDisjoint.mpr (by
        intro p hp q hq hpq
        obtain ⟨i, rfl⟩ := (hF p).mp hp
        obtain ⟨j, rfl⟩ := (hF q).mp hq
        have hij : i ≠ j := fun hij ↦ hpq (by rw [hij])
        exact Clopens.coe_disjoint.mpr (hdisjoint hij))
      sup_parts := hsup
      bot_notMem := by
        intro h
        obtain ⟨i, hi⟩ := (hF _).mp h
        exact (hW i).1 (SetLike.coe_injective hi) }
  refine ⟨P, ?_⟩
  intro p hp
  obtain ⟨i, rfl⟩ := (hF p).mp hp
  obtain ⟨s, hs⟩ := (hW i).2
  refine ⟨(W i).isClopen, lt_of_le_of_lt ?_ (show 2 * (ε / 3) < ε by linarith)⟩
  exact Metric.diam_le_of_subset_closedBall (by positivity)
    (hs.trans Metric.ball_subset_closedBall)

private theorem clopen_inf {S : Type u} [TopologicalSpace S]
    (P Q : Finpartition (Set.univ : Set S))
    (hP : ∀ p ∈ P.parts, IsClopen p) (hQ : ∀ q ∈ Q.parts, IsClopen q) :
    ∀ p ∈ (P ⊓ Q).parts, IsClopen p := by
  classical
  intro p hp
  rw [Finpartition.parts_inf] at hp
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp (Finset.mem_of_mem_erase hp)
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
  exact (hP a ha).inter (hQ b hb)

/-- A compact totally disconnected metric space admits refining finite clopen
partitions whose atoms have diameter less than `2⁻ⁱ`.

Proof: refine the cover by balls of radius `2⁻ⁱ / 3` to a finite pairwise-disjoint
nonempty clopen cover using Mathlib's clopen-cover refinement theorem. Each atom
then has diameter at most `2 * 2⁻ⁱ / 3`. Take successive common refinements, i.e.
infima of finite partitions. An atom of an infimum is a nonempty intersection
of two old atoms, so clopenness is preserved and diameter can only decrease.
Source: Stacks Project, Topology, tag 08ZZ; step 1 of the scalar analytic
expansion of `sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3).
(blueprint: lem-sfb-shrinking-clopen-partitions)
-/
theorem exists_shrinking_clopen_partitions
    (S : Type u) [MetricSpace S] [CompactSpace S] [TotallyDisconnectedSpace S] :
    ∃ P : ℕ+ → Finpartition (Set.univ : Set S),
      (∀ i, P (i + 1) ≤ P i) ∧
      (∀ i p, p ∈ (P i).parts → IsClopen p ∧ Metric.diam p < (1 / 2 : ℝ) ^ (i : ℕ)) := by
  classical
  choose Q hQ using fun i : ℕ+ ↦ exists_small_clopen_partition S
    ((1 / 2 : ℝ) ^ (i : ℕ)) (by positivity)
  let P : ℕ+ → Finpartition (Set.univ : Set S) :=
    fun i ↦ PNat.recOn i (Q 1) (fun n R ↦ R ⊓ Q (n + 1))
  have hPone : P 1 = Q 1 := by simp [P]
  have hPsucc (i : ℕ+) : P (i + 1) = P i ⊓ Q (i + 1) := by simp [P]
  have hPQ (i : ℕ+) : P i ≤ Q i := by
    induction i using PNat.recOn with
    | one => rw [hPone]
    | succ i ih => rw [hPsucc]; exact inf_le_right
  have hclopen (i : ℕ+) : ∀ p ∈ (P i).parts, IsClopen p := by
    induction i using PNat.recOn with
    | one => simpa only [hPone] using fun p hp ↦ (hQ 1 p hp).1
    | succ i ih =>
      rw [hPsucc]
      exact clopen_inf _ _ ih (fun p hp ↦ (hQ (i + 1) p hp).1)
  refine ⟨P, fun i ↦ ?_, ?_⟩
  · rw [hPsucc]
    exact inf_le_left
  · intro i p hp
    obtain ⟨q, hq, hpq⟩ := hPQ i hp
    exact ⟨hclopen i p hp, (Metric.diam_mono hpq
      (isCompact_univ.isBounded.subset (Set.subset_univ _))).trans_lt (hQ i q hq).2⟩

end TopologicalSpace
