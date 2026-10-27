module

public import Mathlib.Data.PNat.Basic
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Data.PNat.Find
import Mathlib.Data.PNat.Interval

/-! # Clopen neighbourhoods and eventually stabilizing least-index selectors.

This is the neighborhood, selector, and pointwise stabilization portion of the
closed-cover construction.
Source: the parent node's scalar analytic expansion, steps 6--8.
(blueprint: lem-sfb-closed-cover-selectors)
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

private noncomputable def leastEligible {S : Type u} (U : ℕ+ → ℕ+ → Set S)
    (i : ℕ+) (s : S) : {j : ℕ+ // j ≤ i} := by
  classical
  exact if h : ∃ j : ℕ+, j ≤ i ∧ s ∈ U j i then
    ⟨PNat.find h, (PNat.find_spec h).1⟩ else ⟨1, one_le⟩

private theorem leastEligible_spec {S : Type u} (U : ℕ+ → ℕ+ → Set S)
    (i : ℕ+) (s : S) :
    ((∃ j : ℕ+, j ≤ i ∧ s ∈ U j i) →
      s ∈ U (leastEligible U i s).val i ∧
        ∀ j : ℕ+, j ≤ i → s ∈ U j i → (leastEligible U i s).val ≤ j) ∧
    ((∀ j : ℕ+, j ≤ i → s ∉ U j i) → (leastEligible U i s).val = 1) := by
  classical
  constructor
  · intro h
    simp only [leastEligible, dif_pos h, Subtype.coe_mk]
    exact ⟨(PNat.find_spec h).2, fun j hji hsj ↦ PNat.find_min' h ⟨hji, hsj⟩⟩
  · intro h
    have hn : ¬ ∃ j : ℕ+, j ≤ i ∧ s ∈ U j i := by
      rintro ⟨j, hji, hsj⟩
      exact h j hji hsj
    simp only [leastEligible, dif_neg hn, Subtype.coe_mk]

private theorem leastEligible_congr {S : Type u} (U : ℕ+ → ℕ+ → Set S)
    (i : ℕ+) {s t : S} (h : ∀ j, j ≤ i → (s ∈ U j i ↔ t ∈ U j i)) :
    leastEligible U i s = leastEligible U i t := by
  apply Subtype.ext
  by_cases hs : ∃ j : ℕ+, j ≤ i ∧ s ∈ U j i
  · obtain ⟨j, hji, hsj⟩ := hs
    have ht : ∃ j : ℕ+, j ≤ i ∧ t ∈ U j i := ⟨j, hji, (h j hji).mp hsj⟩
    have ss := (leastEligible_spec U i s).1 ⟨j, hji, hsj⟩
    have st := (leastEligible_spec U i t).1 ht
    exact le_antisymm
      (ss.2 _ (leastEligible U i t).2 ((h _ (leastEligible U i t).2).mpr st.1))
      (st.2 _ (leastEligible U i s).2 ((h _ (leastEligible U i s).2).mp ss.1))
  · have hns : ∀ j : ℕ+, j ≤ i → s ∉ U j i := by
      intro j hji hsj
      exact hs ⟨j, hji, hsj⟩
    have hnt : ∀ j : ℕ+, j ≤ i → t ∉ U j i := by
      intro j hji htj
      exact hns j hji ((h j hji).mpr htj)
    rw [(leastEligible_spec U i s).2 hns, (leastEligible_spec U i t).2 hnt]

/-- Given shrinking refining clopen partitions, construct the decreasing
neighborhoods of each closed member of a countable cover and the locally
constant least-index selectors that stabilize pointwise.

The proof is the last three steps of the scalar analytic expansion: finite
unions of partition atoms give the neighborhoods, shrinking diameters identify
their intersections with the closed sets, and a finite maximum excludes all
smaller indices at each point.
Source: scalar analytic expansion of paragraph (3), old steps 5--6, of
`sk-thm-sf-ctf-stability-direct-images.proof.md`.
(blueprint: lem-sfb-closed-cover-selectors)
-/
theorem exists_closedCover_selectors
    (S : Type u) [MetricSpace S] [CompactSpace S] [TotallyDisconnectedSpace S]
    (A : ℕ+ → Set S) (hclosed : ∀ j, IsClosed (A j))
    (hcover : (⋃ j, A j) = Set.univ)
    (P : ℕ+ → Finpartition (Set.univ : Set S))
    (hclopen : ∀ i p, p ∈ (P i).parts → IsClopen p)
    (hdiam : ∀ i p, p ∈ (P i).parts → Metric.diam p < (1 / 2 : ℝ) ^ (i : ℕ))
    (hrefine : ∀ i, P (i + 1) ≤ P i) :
    ∃ U : ℕ+ → ℕ+ → Set S,
      (∀ j i, U j i = ⋃ (p : (P i).parts) (_ : (p.val ∩ A j).Nonempty), p.val) ∧
      (∀ j i, IsClopen (U j i)) ∧
      (∀ j i, U j (i + 1) ⊆ U j i) ∧
      (∀ j, (⋂ i, U j i) = A j) ∧
      ∃ k : ∀ i : ℕ+, LocallyConstant S {j : ℕ+ // j ≤ i},
        (∀ i s,
          ((∃ j : ℕ+, j ≤ i ∧ s ∈ U j i) →
            s ∈ U (k i s).val i ∧
              ∀ j : ℕ+, j ≤ i → s ∈ U j i → (k i s).val ≤ j) ∧
          ((∀ j : ℕ+, j ≤ i → s ∉ U j i) → (k i s).val = 1)) ∧
        ∀ s, ∃ j₀ : ℕ+,
          s ∈ A j₀ ∧ (∀ j : ℕ+, s ∈ A j → j₀ ≤ j) ∧
          ∃ i₀ : ℕ+, ∀ i : ℕ+, i₀ ≤ i → (k i s).val = j₀ := by
  classical
  let U : ℕ+ → ℕ+ → Set S := fun j i ↦
    ⋃ (p : (P i).parts) (_ : (p.val ∩ A j).Nonempty), p.val
  have hmem (j i : ℕ+) (s : S) :
      s ∈ U j i ↔ ∃ p ∈ (P i).parts, s ∈ p ∧ (p ∩ A j).Nonempty := by
    simp only [U, Set.mem_iUnion]
    constructor
    · rintro ⟨p, hmeet, hsp⟩
      exact ⟨p.val, p.property, hsp, hmeet⟩
    · rintro ⟨p, hp, hsp, hmeet⟩
      exact ⟨⟨p, hp⟩, hmeet, hsp⟩
  have hcontains (j i : ℕ+) : A j ⊆ U j i := by
    intro s hs
    obtain ⟨p, hp, hsp⟩ := partition_covers (P i) s
    exact (hmem j i s).mpr ⟨p, hp, hsp, s, hsp, hs⟩
  have hdec (j i : ℕ+) : U j (i + 1) ⊆ U j i := by
    intro s hs
    obtain ⟨p, hp, hsp, a, hap, haA⟩ := (hmem j (i + 1) s).mp hs
    obtain ⟨q, hq, hpq⟩ := hrefine i hp
    exact (hmem j i s).mpr ⟨q, hq, hpq hsp, a, hpq hap, haA⟩
  have hanti (j : ℕ+) : Antitone (U j) := by
    intro i k
    refine PNat.recOn k ?_ ?_ i
    · intro i hi
      have hi1 : i = 1 := le_antisymm hi (one_le)
      simp [hi1]
    · intro k ih i hi
      rcases eq_or_lt_of_le hi with heq | hlt
      · simp [heq]
      · exact (hdec j k).trans (ih i (PNat.lt_add_one_iff.mp hlt))
  have hinter (j : ℕ+) : (⋂ i, U j i) = A j := by
    apply Set.Subset.antisymm
    · intro s hs
      by_contra hn
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hclosed j).isOpen_compl s hn
      obtain ⟨n, hnε⟩ : ∃ n : ℕ, (1 / 2 : ℝ) ^ n < ε :=
        exists_pow_lt_of_lt_one hε (by norm_num)
      let i : ℕ+ := n.succPNat
      have hiε : (1 / 2 : ℝ) ^ (i : ℕ) < ε := by
        exact lt_of_le_of_lt (pow_le_pow_of_le_one (by norm_num) (by norm_num)
          (show n ≤ (i : ℕ) by exact Nat.le_succ n)) hnε
      obtain ⟨p, hp, hsp, a, hap, haA⟩ :=
        (hmem j i s).mp (Set.mem_iInter.mp hs i)
      have hdist : dist a s < ε :=
        (Metric.dist_le_diam_of_mem
          (isCompact_univ.isBounded.subset (Set.subset_univ p)) hap hsp).trans_lt
          ((hdiam i p hp).trans hiε)
      exact hball hdist haA
    · exact Set.subset_iInter fun i ↦ hcontains j i
  have hconst (j i : ℕ+) {p : Set S} (hp : p ∈ (P i).parts)
      {s t : S} (hs : s ∈ p) (ht : t ∈ p) : s ∈ U j i ↔ t ∈ U j i := by
    have hforward : ∀ {s t : S}, s ∈ p → t ∈ p → s ∈ U j i → t ∈ U j i := by
      intro s t hs ht hsu
      obtain ⟨q, hq, hsq, hmeet⟩ := (hmem j i s).mp hsu
      have heq := partition_unique (P i) hq hp hsq hs
      exact (hmem j i t).mpr ⟨p, hp, ht, heq ▸ hmeet⟩
    exact ⟨hforward hs ht, hforward ht hs⟩
  have hlc (i : ℕ+) : IsLocallyConstant (leastEligible U i) := by
    rw [IsLocallyConstant.iff_exists_open]
    intro s
    obtain ⟨p, hp, hsp⟩ := partition_covers (P i) s
    refine ⟨p, (hclopen i p hp).isOpen, hsp, ?_⟩
    intro t htp
    exact leastEligible_congr U i fun j _ ↦ hconst j i hp htp hsp
  let k : ∀ i : ℕ+, LocallyConstant S {j : ℕ+ // j ≤ i} :=
    fun i ↦ ⟨leastEligible U i, hlc i⟩
  refine ⟨U, fun _ _ ↦ rfl, ?_, hdec, hinter, k, ?_, ?_⟩
  · intro j i
    apply isClopen_iUnion_of_finite
    intro p
    apply isClopen_iUnion_of_finite
    intro _
    exact hclopen i p.val p.property
  · exact fun i s ↦ leastEligible_spec U i s
  · intro s
    have hex : ∃ j : ℕ+, s ∈ A j := by
      have : s ∈ ⋃ j, A j := hcover.symm ▸ Set.mem_univ s
      exact Set.mem_iUnion.mp this
    let j₀ := PNat.find hex
    have hsA : s ∈ A j₀ := PNat.find_spec hex
    have hmin : ∀ j, s ∈ A j → j₀ ≤ j := fun _ hj ↦ PNat.find_min' hex hj
    have hexclude : ∀ j < j₀, ∃ n : ℕ+, s ∉ U j n := by
      intro j hj
      by_contra hn
      have hall : ∀ n : ℕ+, s ∈ U j n := by simpa using hn
      have hsAj : s ∈ A j := hinter j ▸ Set.mem_iInter.mpr hall
      exact (not_le_of_gt hj) (hmin j hsAj)
    have hfinite : ∃ n : ℕ+, ∀ j ∈ Finset.Ico (1 : ℕ+) j₀,
        ∀ i : ℕ+, n ≤ i → s ∉ U j i := by
      have haux : ∀ F : Finset ℕ+, (∀ j ∈ F, j < j₀) →
          ∃ n : ℕ+, ∀ j ∈ F, ∀ i : ℕ+, n ≤ i → s ∉ U j i := by
        intro F
        induction F using Finset.induction_on with
        | empty => exact fun _ ↦ ⟨1, by simp⟩
        | @insert j F hj ih =>
          intro hF
          obtain ⟨n, hn⟩ := ih (fun l hl ↦ hF l (Finset.mem_insert_of_mem hl))
          obtain ⟨m, hm⟩ := hexclude j (hF j (Finset.mem_insert_self j F))
          refine ⟨max n m, ?_⟩
          intro l hl i hi
          rcases Finset.mem_insert.mp hl with rfl | hl
          · exact fun hsi ↦ hm (hanti l ((le_max_right n m).trans hi) hsi)
          · exact hn l hl i ((le_max_left n m).trans hi)
      exact haux _ (fun j hj ↦ (Finset.mem_Ico.mp hj).2)
    obtain ⟨n, hn⟩ := hfinite
    refine ⟨j₀, hsA, hmin, max j₀ n, ?_⟩
    intro i hi
    have hj₀i : j₀ ≤ i := (le_max_left j₀ n).trans hi
    have hni : n ≤ i := (le_max_right j₀ n).trans hi
    have helig : ∃ j : ℕ+, j ≤ i ∧ s ∈ U j i :=
      ⟨j₀, hj₀i, hcontains j₀ i hsA⟩
    have hspec := (leastEligible_spec U i s).1 helig
    apply le_antisymm (hspec.2 j₀ hj₀i (hcontains j₀ i hsA))
    apply le_of_not_gt
    intro hlt
    exact hn _ (Finset.mem_Ico.mpr ⟨one_le, hlt⟩) i hni hspec.1

end TopologicalSpace
