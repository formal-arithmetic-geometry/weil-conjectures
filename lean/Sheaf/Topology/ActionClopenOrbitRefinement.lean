module

public import Mathlib.Data.Setoid.Partition
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Compactness.Compact
import Mathlib.Data.Fintype.Pi

/-! # Finite orbits and invariant refinements of clopen partitions

Source: Bhatt–Scholze, The pro-étale topology for schemes, Example 4.1.10, p. 28,
agent expansion of the invariant finite-quotient construction
(blueprint: lem-sfb-action-clopen-orbit-refinement).

The orbit and its common refinement are specified by literal set formulas. In particular,
the refinement consists of all nonempty intersections of one block from each orbit member.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open Filter Topology

namespace MulAction

/-- Every finite clopen partition has a blockwise stabilizing open normal subgroup,
a finite orbit, and the indicated invariant common refinement.

Source: Bhatt–Scholze, Example 4.1.10, p. 28, agent expansion of the invariant
finite-quotient construction (blueprint: lem-sfb-action-clopen-orbit-refinement).

Proof:
1. If P is empty, its partition is empty, its orbit consists of that empty partition,
   and there is no choice of a block from that orbit member. The refinement is empty;
   take the whole group as N. Otherwise each clopen block is compact by
   lem-weil-pbc-closed-in-quasi-compact (IsClosed.isCompact).
2. For each block A, the inverse image of A under the action is an open neighborhood
   of {1} × A. Apply lem-sfb-compact-product-open-neighborhoods
   (generalized_tube_lemma) to obtain an open neighborhood U_A of 1 with U_A A ⊆ A.
3. Intersect the finitely many U_A and choose an open normal subgroup N inside it.
   For n in N, both nA ⊆ A and n⁻¹A ⊆ A hold, hence nA = A.
4. Compactness gives a finite cover of G by left cosets of N. A translate of the
   partition depends only on that coset, so its orbit T is finite.
5. Translates are finite clopen partitions. There are only finitely many choices of
   a block from each member of T; their nonempty intersections are clopen, disjoint,
   and cover P. Since the original partition belongs to T, they refine it.
6. Multiplication by g permutes T and carries each such intersection to the
   intersection of its translated blocks. Applying g⁻¹ gives equality of the block sets.
-/
theorem exists_openNormalSubgroup_finite_clopen_orbit_refinement
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G]
    (hN : ∀ U ∈ 𝓝 (1 : G), ∃ N : OpenNormalSubgroup G, (N : Set G) ⊆ U)
    (P : Type v) [TopologicalSpace P] [CompactSpace P]
    [MulAction G P] [ContinuousSMul G P]
    (α : Set (Set P)) (hfinite : α.Finite) (hpartition : Setoid.IsPartition α)
    (hclopen : ∀ A ∈ α, IsClopen A) :
    (∃ N : OpenNormalSubgroup G,
      ∀ n ∈ N, ∀ A ∈ α, (fun p : P ↦ n • p) '' A = A) ∧
    ∃ (T : Set (Set (Set P))) (β : Set (Set P)),
      T = Set.range (fun g : G ↦ (fun A : Set P ↦ (fun p : P ↦ g • p) '' A) '' α) ∧
      T.Finite ∧
      β = {B : Set P | B.Nonempty ∧ ∃ f : T → Set P,
        (∀ γ : T, f γ ∈ γ.val) ∧ B = ⋂ γ : T, f γ} ∧
      β.Finite ∧ Setoid.IsPartition β ∧ (∀ B ∈ β, IsClopen B) ∧
      (∀ B ∈ β, ∃ A ∈ α, B ⊆ A) ∧
      ∀ g : G, (fun B : Set P ↦ (fun p : P ↦ g • p) '' B) '' β = β := by
  classical
  have hsmall (A : Set P) (hA : A ∈ α) :
      ∃ U : Set G, IsOpen U ∧ 1 ∈ U ∧
        ∀ n ∈ U, ∀ p ∈ A, n • p ∈ A := by
    obtain ⟨U, V, hU, _, h1, hV, hUV⟩ := generalized_tube_lemma
      (isCompact_singleton (x := (1 : G))) (hclopen A hA).isClosed.isCompact
      ((hclopen A hA).isOpen.preimage continuous_smul)
      (by
        rintro ⟨g, p⟩ ⟨hg, hp⟩
        change g • p ∈ A
        have hg1 : g = 1 := Set.mem_singleton_iff.mp hg
        simpa only [hg1, one_smul] using hp)
    refine ⟨U, hU, h1 (Set.mem_singleton 1), fun n hn p hp ↦ ?_⟩
    exact hUV (show (n, p) ∈ U ×ˢ V from ⟨hn, hV hp⟩)
  choose U hU h1 hUA using hsmall
  have hnhds : (⋂ A : α, U A.val A.property) ∈ 𝓝 (1 : G) := by
    let := hfinite.fintype
    exact (isOpen_iInter_of_finite fun (A : α) ↦ hU A.val A.property).mem_nhds
      (Set.mem_iInter.mpr fun (A : α) ↦ h1 A.val A.property)
  obtain ⟨N, hNU⟩ := hN _ hnhds
  have hfix (n : G) (hn : n ∈ N) (A : Set P) (hA : A ∈ α) :
      (fun p : P ↦ n • p) '' A = A := by
    have hsub (m : G) (hm : m ∈ N) : ∀ p ∈ A, m • p ∈ A :=
      hUA A hA m (Set.mem_iInter.mp (hNU hm) ⟨A, hA⟩)
    apply Set.Subset.antisymm
    · rintro _ ⟨p, hp, rfl⟩
      exact hsub n hn p hp
    · intro p hp
      exact ⟨n⁻¹ • p, hsub n⁻¹ (N.inv_mem hn) p hp, smul_inv_smul n p⟩
  refine ⟨⟨N, hfix⟩, ?_⟩
  let act (g : G) (A : Set P) := (fun p : P ↦ g • p) '' A
  let tr (g : G) (γ : Set (Set P)) := act g '' γ
  have act_mul (g h : G) (A : Set P) : act g (act h A) = act (g * h) A := by
    simp only [act, Set.image_image, ← mul_smul]
  have act_one (A : Set P) : act 1 A = A := by simp [act]
  have tr_mul (g h : G) (γ : Set (Set P)) : tr g (tr h γ) = tr (g * h) γ := by
    simp only [tr, Set.image_image, act_mul]
  have tr_one (γ : Set (Set P)) : tr 1 γ = γ := by simp [tr, act_one]
  let T := Set.range (fun g : G ↦ tr g α)
  have hTfinite : T.Finite := by
    obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
      (fun g : G ↦ (fun n : G ↦ g * n) '' (N : Set G))
      (fun g ↦ isOpenMap_mul_left g _ N.isOpen)
      (by intro g _; exact Set.mem_iUnion.mpr ⟨g, 1, N.one_mem, mul_one g⟩)
    apply (s.finite_toSet.image (fun g ↦ tr g α)).subset
    rintro γ ⟨g, rfl⟩
    obtain ⟨i, hi, n, hn, hgin⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ g))
    refine ⟨i, hi, ?_⟩
    change tr i α = tr g α
    rw [← hgin]
    change tr i α = tr (i * n) α
    rw [← tr_mul]
    congr 1
    symm
    apply Set.Subset.antisymm
    · rintro _ ⟨A, hA, rfl⟩
      change ((fun p : P ↦ n • p) '' A) ∈ α
      rw [hfix n hn A hA]
      exact hA
    · intro A hA
      exact ⟨A, hA, hfix n hn A hA⟩
  have hT (g : G) (γ : T) : tr g γ.val ∈ T := by
    obtain ⟨h, hh⟩ := γ.property
    refine ⟨g * h, ?_⟩
    change tr (g * h) α = tr g γ.val
    change tr h α = γ.val at hh
    rw [← tr_mul, hh]
  have hαT : α ∈ T := ⟨1, tr_one α⟩
  have hparts (γ : T) : Setoid.IsPartition γ.val := by
    obtain ⟨g, hg⟩ := γ.property
    rw [← hg]
    constructor
    · rintro ⟨A, hA, he⟩
      obtain ⟨p, hp⟩ := Setoid.nonempty_of_mem_partition hpartition hA
      exact Set.notMem_empty (g • p) (he ▸ (Set.mem_image_of_mem _ hp))
    · intro p
      obtain ⟨A, ⟨hA, hp⟩, huniq⟩ := hpartition.2 (g⁻¹ • p)
      refine ⟨act g A, ⟨⟨A, hA, rfl⟩, ?_⟩, ?_⟩
      · exact ⟨g⁻¹ • p, hp, smul_inv_smul g p⟩
      · rintro B ⟨⟨C, hC, rfl⟩, q, hq, he⟩
        have hq' : g⁻¹ • p ∈ C := by simpa [← he] using hq
        exact congrArg (act g) (huniq C ⟨hC, hq'⟩)
  have hγfinite (γ : T) : γ.val.Finite := by
    obtain ⟨g, hg⟩ := γ.property
    rw [← hg]
    exact hfinite.image _
  have hγclopen (γ : T) (A : Set P) (hA : A ∈ γ.val) : IsClopen A := by
    obtain ⟨g, hg⟩ := γ.property
    rw [← hg] at hA
    obtain ⟨B, hB, rfl⟩ := hA
    have he : act g B = (fun p : P ↦ g⁻¹ • p) ⁻¹' B := by
      ext p
      constructor
      · rintro ⟨q, hq, rfl⟩; simpa using hq
      · intro hp; exact ⟨g⁻¹ • p, hp, smul_inv_smul g p⟩
    rw [he]
    exact (hclopen B hB).preimage (continuous_const_smul _)
  let β : Set (Set P) := {B | B.Nonempty ∧ ∃ f : T → Set P,
    (∀ γ : T, f γ ∈ γ.val) ∧ B = ⋂ γ : T, f γ}
  let := hTfinite.fintype
  have hβeq (B C : Set P) (hB : B ∈ β) (hC : C ∈ β) (p : P)
      (hpB : p ∈ B) (hpC : p ∈ C) : B = C := by
    obtain ⟨_, f, hf, rfl⟩ := hB
    obtain ⟨_, k, hk, rfl⟩ := hC
    congr 1
    funext γ
    exact Setoid.eq_of_mem_eqv_class (hparts γ).2 (hf γ)
      (Set.mem_iInter.mp hpB γ) (hk γ) (Set.mem_iInter.mp hpC γ)
  have hβcover (p : P) : ∃ B ∈ β, p ∈ B := by
    have hex (γ : T) : ∃ A : Set P, A ∈ γ.val ∧ p ∈ A :=
      (hparts γ).2 p |>.exists
    choose f hf hp using hex
    refine ⟨⋂ γ : T, f γ, ⟨?_, f, hf, rfl⟩, ?_⟩
    · exact ⟨p, Set.mem_iInter.mpr hp⟩
    · exact Set.mem_iInter.mpr hp
  have hβmap (g : G) (B : Set P) (hB : B ∈ β) : act g B ∈ β := by
    obtain ⟨⟨p, hp⟩, f, hf, rfl⟩ := hB
    let prev (γ : T) : T := ⟨tr g⁻¹ γ.val, hT g⁻¹ γ⟩
    let k (γ : T) : Set P := act g (f (prev γ))
    have hk (γ : T) : k γ ∈ γ.val := by
      have hm : k γ ∈ tr g (tr g⁻¹ γ.val) := ⟨f (prev γ), hf (prev γ), rfl⟩
      simpa only [tr_mul, mul_inv_cancel, tr_one] using hm
    refine ⟨⟨g • p, Set.mem_image_of_mem _ hp⟩, k, hk, ?_⟩
    ext q
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact Set.mem_iInter.mpr fun γ ↦ ⟨r, Set.mem_iInter.mp hr (prev γ), rfl⟩
    · intro hq
      refine ⟨g⁻¹ • q, Set.mem_iInter.mpr fun γ ↦ ?_, smul_inv_smul g q⟩
      let next : T := ⟨tr g γ.val, hT g γ⟩
      have he : prev next = γ := by
        apply Subtype.ext
        exact (tr_mul g⁻¹ g γ.val).trans (by rw [inv_mul_cancel, tr_one])
      obtain ⟨r, hr, hrq⟩ := Set.mem_iInter.mp hq next
      have heq : g⁻¹ • q = r := by rw [← hrq]; exact inv_smul_smul g r
      rw [heq]
      simpa only [he] using hr
  refine ⟨T, β, rfl, hTfinite, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · have hf : {f : T → Set P | ∀ γ, f γ ∈ γ.val}.Finite :=
      Set.Finite.pi' hγfinite
    apply (hf.image (fun f ↦ ⋂ γ : T, f γ)).subset
    rintro B ⟨_, f, hf, rfl⟩
    exact ⟨f, hf, rfl⟩
  · refine ⟨fun h ↦ h.1.ne_empty rfl, fun p ↦ ?_⟩
    obtain ⟨B, hB, hp⟩ := hβcover p
    exact ⟨B, ⟨hB, hp⟩, fun C hC ↦ hβeq C B hC.1 hB p hC.2 hp⟩
  · rintro B ⟨_, f, hf, rfl⟩
    exact isClopen_iInter_of_finite fun γ ↦ hγclopen γ (f γ) (hf γ)
  · rintro B ⟨_, f, hf, rfl⟩
    exact ⟨f ⟨α, hαT⟩, hf ⟨α, hαT⟩, Set.iInter_subset _ (⟨α, hαT⟩ : T)⟩
  · intro g
    apply Set.Subset.antisymm
    · rintro _ ⟨B, hB, rfl⟩
      exact hβmap g B hB
    · intro B hB
      refine ⟨act g⁻¹ B, hβmap g⁻¹ B hB, ?_⟩
      change act g (act g⁻¹ B) = B
      rw [act_mul, mul_inv_cancel, act_one]

end MulAction
