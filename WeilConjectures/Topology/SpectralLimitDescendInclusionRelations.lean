/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Topology.Spectral.Hom
public import Mathlib.Topology.Spectral.ConstructibleTopology
import Mathlib.Topology.Spectral.Basic
import Mathlib.Topology.Spectral.ConstructibleTopology
import Mathlib.Topology.Spectral.Hom
import Mathlib.Topology.Category.TopCat.Limits.Konig
import WeilConjectures.SixFunctors.ConstructibleTopologyHausdorff
import WeilConjectures.Mathlib.Topology.Spectral.ConstructibleTopology
import WeilConjectures.Topology.SpectralLimitConstructibleClosed

@[expose] public section

universe u v w

namespace Topology

/-- In an inverse system of nonempty closed subsets `Z i` of compact Hausdorff spaces, indexed
by a directed preorder, there is a compatible family `a` with `a i ∈ Z i` for every `i`. -/
theorem exists_compatible_mem_of_isClosed {I : Type u} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (S : I → Type v) [t : ∀ i : I, TopologicalSpace (S i)]
    [hc : ∀ i : I, CompactSpace (S i)] [ht : ∀ i : I, T2Space (S i)]
    (f : ∀ (i j : I), i ≤ j → S j → S i) (hf : ∀ (i j : I) (h : i ≤ j), Continuous (f i j h))
    (hfcomp : ∀ (i j k : I) (hij : i ≤ j) (hjk : j ≤ k) (x : S k),
      f i j hij (f j k hjk x) = f i k (hij.trans hjk) x)
    (Z : ∀ i : I, Set (S i)) (hZ : ∀ i : I, IsClosed (Z i))
    (hZf : ∀ (i j : I) (h : i ≤ j), Set.MapsTo (f i j h) (Z j) (Z i))
    (hne : ∀ i : I, (Z i).Nonempty) :
    ∃ a : ∀ i : I, S i, (∀ (i j : I) (h : i ≤ j), f i j h (a j) = a i) ∧ ∀ i : I, a i ∈ Z i := by
  classical
  let C : I → Set (∀ i : I, S i) := fun k ↦
    {a | a k ∈ Z k ∧ ∀ (i j : I) (h : i ≤ j), j ≤ k → f i j h (a j) = a i}
  have hCcl (k : I) : IsClosed (C k) := by
    simp only [C, Set.ofPred_and, Set.ofPred_forall]
    exact ((hZ k).preimage (continuous_apply k)).inter <| isClosed_iInter fun i ↦
      isClosed_iInter fun j ↦ isClosed_iInter fun h ↦ isClosed_iInter fun _ ↦
        isClosed_eq ((hf i j h).comp (continuous_apply j)) (continuous_apply i)
  have hCne (k : I) : (C k).Nonempty := by
    obtain ⟨e, he⟩ := hne k
    refine ⟨fun m ↦ if h : m ≤ k then f m k h e else (hne m).some, ?_, ?_⟩
    · simpa using hZf k k le_rfl he
    · intro i j h hjk
      simp only [dif_pos hjk, dif_pos (h.trans hjk)]
      exact hfcomp i j k h hjk e
  have hCanti (k l : I) (hkl : k ≤ l) : C l ⊆ C k := by
    rintro a ⟨haZ, hac⟩
    refine ⟨?_, fun i j h hjk ↦ hac i j h (hjk.trans hkl)⟩
    rw [← hac k l hkl le_rfl]
    exact hZf k l hkl haZ
  have hCdir : Directed (· ⊇ ·) C := by
    intro k l
    obtain ⟨m, hkm, hlm⟩ := directed_of (· ≤ ·) k l
    exact ⟨m, hCanti k m hkm, hCanti l m hlm⟩
  obtain ⟨a, ha⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed C hCdir
    hCne (fun k ↦ (hCcl k).isCompact) hCcl
  rw [Set.mem_iInter] at ha
  exact ⟨a, fun i j h ↦ (ha j).2 i j h le_rfl, fun i ↦ (ha i).1⟩

/-- The spectral version of `exists_compatible_mem_of_isClosed`: for an inverse system of
spectral spaces and spectral maps, nonempty compatible subsets which are closed in the
constructible topology admit a compatible family of points. -/
theorem exists_compatible_mem_of_isClosed_constructibleTopology {I : Type u} [Preorder I]
    [Nonempty I] [IsDirected I (· ≤ ·)] (S : I → Type v) [∀ i : I, TopologicalSpace (S i)]
    [∀ i : I, SpectralSpace (S i)] (f : ∀ (i j : I), i ≤ j → S j → S i)
    (hf : ∀ (i j : I) (h : i ≤ j), IsSpectralMap (f i j h))
    (hfcomp : ∀ (i j k : I) (hij : i ≤ j) (hjk : j ≤ k) (x : S k),
      f i j hij (f j k hjk x) = f i k (hij.trans hjk) x)
    (Z : ∀ i : I, Set (S i)) (hZ : ∀ i : I, IsClosed[constructibleTopology (S i)] (Z i))
    (hZf : ∀ (i j : I) (h : i ≤ j), Set.MapsTo (f i j h) (Z j) (Z i))
    (hne : ∀ i : I, (Z i).Nonempty) :
    ∃ a : ∀ i : I, S i, (∀ (i j : I) (h : i ≤ j), f i j h (a j) = a i) ∧ ∀ i : I, a i ∈ Z i :=
  exists_compatible_mem_of_isClosed (t := fun i ↦ constructibleTopology (S i))
    (hc := fun i ↦ @Function.Surjective.compactSpace (WithConstructibleTopology (S i)) (S i)
      _ (constructibleTopology (S i)) _ (WithTopology.continuous_ofTopology _) inferInstance
      (WithTopology.ofTopology_surjective _))
    (ht := fun i ↦ t2Space_constructibleTopology (S i))
    S f (fun i j h ↦ (hf i j h).continuous_constructibleTopology) hfcomp Z hZ hZf hne

/-- Inclusion clause of spectral inverse-limit descent (Stacks Project, Tag 0A30, part (2)):
if the pullbacks of quasi-compact opens `U ⊆ S i` and `V ⊆ S j` to the limit satisfy
`p i ⁻¹' U ⊆ p j ⁻¹' V`, the inclusion already holds at some common upper stage. -/
theorem spectralLimit_descend_subset {I : Type u} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (S : I → Type u) [∀ i : I, TopologicalSpace (S i)]
    [∀ i : I, SpectralSpace (S i)] (f : ∀ (i j : I), i ≤ j → S j → S i)
    (hf : ∀ (i j : I) (h : i ≤ j), IsSpectralMap (f i j h))
    (hfcomp : ∀ (i j k : I) (hij : i ≤ j) (hjk : j ≤ k) (x : S k),
      f i j hij (f j k hjk x) = f i k (hij.trans hjk) x)
    {X : Type v} (p : ∀ i : I, X → S i)
    (hpcomp : ∀ (i j : I) (h : i ≤ j) (x : X), f i j h (p j x) = p i x)
    (hlimit : ∀ a : ∀ i : I, S i,
      (∀ (i j : I) (h : i ≤ j), f i j h (a j) = a i) →
      ∃! x : X, ∀ i : I, p i x = a i)
    (i j : I) (U : Set (S i)) (V : Set (S j)) (hUo : IsOpen U) (hUc : IsCompact U)
    (hVo : IsOpen V) (hVc : IsCompact V) (hUV : p i ⁻¹' U ⊆ p j ⁻¹' V) :
    ∃ (k : I) (hik : i ≤ k) (hjk : j ≤ k), f i k hik ⁻¹' U ⊆ f j k hjk ⁻¹' V := by
  obtain ⟨k₀, hik₀, hjk₀⟩ := directed_of (· ≤ ·) i j
  by_contra hcon
  simp only [not_exists] at hcon
  let Z : ∀ k : I, Set (S k) := fun k ↦
    ⋂ h : k₀ ≤ k, f i k (hik₀.trans h) ⁻¹' U ∩ (f j k (hjk₀.trans h) ⁻¹' V)ᶜ
  have hZf (k l : I) (hkl : k ≤ l) : Set.MapsTo (f k l hkl) (Z l) (Z k) := by
    intro s hs
    simp only [Z, Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff]
      at hs ⊢
    intro h
    rw [hfcomp, hfcomp]
    exact hs (h.trans hkl)
  have hZ (k : I) : IsClosed[constructibleTopology (S k)] (Z k) := by
    refine @isClosed_iInter _ _ (constructibleTopology (S k)) _ fun h ↦ ?_
    refine @IsClosed.inter _ _ _ (constructibleTopology (S k))
      (((hf i k _).isCompact_preimage_of_isOpen hUo hUc).isClosed_constructibleTopology_of_isOpen
        (hUo.preimage (hf i k _).continuous))
      ((@isClosed_compl_iff _ (constructibleTopology (S k)) _).mpr ?_)
    exact ((hf j k _).isCompact_preimage_of_isOpen hVo hVc).isOpen_constructibleTopology_of_isOpen
      (hVo.preimage (hf j k _).continuous)
  have hne (k : I) : (Z k).Nonempty := by
    obtain ⟨l, hkl, hl⟩ := directed_of (· ≤ ·) k k₀
    obtain ⟨s, hsU, hsV⟩ := Set.not_subset.mp (hcon l (hik₀.trans hl) (hjk₀.trans hl))
    refine ⟨f k l hkl s, hZf k l hkl ?_⟩
    simp only [Z, Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff]
    exact fun _ ↦ ⟨hsU, hsV⟩
  obtain ⟨a, hac, haZ⟩ :=
    exists_compatible_mem_of_isClosed_constructibleTopology S f hf hfcomp Z hZ hZf hne
  obtain ⟨x, hx, -⟩ := hlimit a hac
  obtain ⟨h1, h2⟩ := Set.mem_iInter.mp (haZ k₀) le_rfl
  rw [Set.mem_preimage, ← hx, hpcomp] at h1
  rw [Set.mem_compl_iff, Set.mem_preimage, ← hx, hpcomp] at h2
  exact h2 (hUV h1)

/-- Equality clause of spectral inverse-limit descent: if two quasi-compact opens of `S i` have
the same pullback to the limit, their pullbacks agree at some later stage. -/
theorem spectralLimit_descend_eq {I : Type u} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (S : I → Type u) [∀ i : I, TopologicalSpace (S i)]
    [∀ i : I, SpectralSpace (S i)] (f : ∀ (i j : I), i ≤ j → S j → S i)
    (hf : ∀ (i j : I) (h : i ≤ j), IsSpectralMap (f i j h))
    (hfcomp : ∀ (i j k : I) (hij : i ≤ j) (hjk : j ≤ k) (x : S k),
      f i j hij (f j k hjk x) = f i k (hij.trans hjk) x)
    {X : Type v} (p : ∀ i : I, X → S i)
    (hpcomp : ∀ (i j : I) (h : i ≤ j) (x : X), f i j h (p j x) = p i x)
    (hlimit : ∀ a : ∀ i : I, S i,
      (∀ (i j : I) (h : i ≤ j), f i j h (a j) = a i) →
      ∃! x : X, ∀ i : I, p i x = a i)
    (i : I) (U W : Set (S i)) (hUo : IsOpen U) (hUc : IsCompact U)
    (hWo : IsOpen W) (hWc : IsCompact W) (hUW : p i ⁻¹' U = p i ⁻¹' W) :
    ∃ (j : I) (hij : i ≤ j), f i j hij ⁻¹' U = f i j hij ⁻¹' W := by
  obtain ⟨k, hik, _, hk⟩ := spectralLimit_descend_subset S f hf hfcomp p hpcomp hlimit
    i i U W hUo hUc hWo hWc hUW.subset
  obtain ⟨k', hik', _, hk'⟩ := spectralLimit_descend_subset S f hf hfcomp p hpcomp hlimit
    i i W U hWo hWc hUo hUc hUW.symm.subset
  obtain ⟨j, hkj, hk'j⟩ := directed_of (· ≤ ·) k k'
  have hpre (m : I) (him : i ≤ m) (hmj : m ≤ j) (A : Set (S i)) :
      f i j (him.trans hmj) ⁻¹' A = f m j hmj ⁻¹' (f i m him ⁻¹' A) := by
    ext s
    simp [hfcomp]
  refine ⟨j, hik.trans hkj, Set.Subset.antisymm ?_ ?_⟩
  · rw [hpre k hik hkj, hpre k hik hkj]
    exact Set.preimage_mono hk
  · rw [hpre k' hik' hk'j, hpre k' hik' hk'j]
    exact Set.preimage_mono hk'

/-- The inclusion and finite equality clauses in spectral inverse-limit descent.
This is the strict lower-level core of `spectralLimit_descend_opens`; its proof follows
Stacks Project, Topology, Lemma 0A30, parts (2)--(4), using the constructibly closed
nonempty compatible-point lemma for part (2), then finite unions and intersections.
(blueprint: lem-weil-pbc-spectral-limit-descend-inclusion-relations)

Proof in words: for an inclusion, take the constructibly closed differences over the
cofinal upper tail. If every difference were nonempty, the compatible-point theorem
would give a family contradicting the inclusion on X. Thus one difference is empty.
Apply this inclusion result in both directions to the finite union or intersection of
the given compact opens, then pass to a common upper stage. -/
theorem spectralLimit_descend_inclusion_relations
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (S : I → Type u) [∀ i : I, TopologicalSpace (S i)] [∀ i : I, SpectralSpace (S i)]
    (f : ∀ (i j : I), i ≤ j → S j → S i)
    (hf : ∀ (i j : I) (h : i ≤ j), IsSpectralMap (f i j h))
    (hfid : ∀ (i : I) (x : S i), f i i le_rfl x = x)
    (hfcomp : ∀ (i j k : I) (hij : i ≤ j) (hjk : j ≤ k) (x : S k),
      f i j hij (f j k hjk x) = f i k (hij.trans hjk) x)
    (X : Type v) [TopologicalSpace X] (p : ∀ i : I, X → S i)
    (hpcomp : ∀ (i j : I) (h : i ≤ j) (x : X), f i j h (p j x) = p i x)
    (hlimit : ∀ a : ∀ i : I, S i,
      (∀ (i j : I) (h : i ≤ j), f i j h (a j) = a i) →
      ∃! x : X, ∀ i : I, p i x = a i) :
    (∀ (i j : I) (U : Set (S i)) (V : Set (S j)),
      IsOpen U → IsCompact U → IsOpen V → IsCompact V →
      p i ⁻¹' U ⊆ p j ⁻¹' V →
      ∃ (k : I) (hik : i ≤ k) (hjk : j ≤ k),
        f i k hik ⁻¹' U ⊆ f j k hjk ⁻¹' V) ∧
    (∀ (i : I) (n : ℕ) (U : Set (S i)) (V : Fin n → Set (S i)),
      IsOpen U → IsCompact U → (∀ l : Fin n, IsOpen (V l) ∧ IsCompact (V l)) →
      p i ⁻¹' U = ⋃ l : Fin n, p i ⁻¹' V l →
      ∃ (j : I) (hij : i ≤ j),
        f i j hij ⁻¹' U = ⋃ l : Fin n, f i j hij ⁻¹' V l) ∧
    (∀ (i : I) (n : ℕ) (U : Set (S i)) (V : Fin n → Set (S i)),
      IsOpen U → IsCompact U → (∀ l : Fin n, IsOpen (V l) ∧ IsCompact (V l)) →
      p i ⁻¹' U = ⋂ l : Fin n, p i ⁻¹' V l →
      ∃ (j : I) (hij : i ≤ j),
        f i j hij ⁻¹' U = ⋂ l : Fin n, f i j hij ⁻¹' V l) := by
  refine ⟨spectralLimit_descend_subset S f hf hfcomp p hpcomp hlimit,
    fun i n U V hUo hUc hV hUV ↦ ?_, fun i n U V hUo hUc hV hUV ↦ ?_⟩
  · obtain ⟨j, hij, hj⟩ := spectralLimit_descend_eq S f hf hfcomp p hpcomp hlimit i U
      (⋃ l, V l) hUo hUc (isOpen_iUnion fun l ↦ (hV l).1) (isCompact_iUnion fun l ↦ (hV l).2)
      (by rw [Set.preimage_iUnion, hUV])
    refine ⟨j, hij, ?_⟩
    rw [hj, Set.preimage_iUnion]
  · have hWc : IsCompact (⋂ l, V l) := by
      rw [← Set.sInter_range]
      refine QuasiSeparatedSpace.isCompact_sInter (Set.finite_range V) ?_ ?_
      · rintro _ ⟨l, rfl⟩
        exact Or.inl (hV l).1
      · rintro _ ⟨l, rfl⟩
        exact (hV l).2
    obtain ⟨j, hij, hj⟩ := spectralLimit_descend_eq S f hf hfcomp p hpcomp hlimit i U
      (⋂ l, V l) hUo hUc (isOpen_iInter_of_finite fun l ↦ (hV l).1) hWc
      (by rw [Set.preimage_iInter, hUV])
    refine ⟨j, hij, ?_⟩
    rw [hj, Set.preimage_iInter]

end Topology
