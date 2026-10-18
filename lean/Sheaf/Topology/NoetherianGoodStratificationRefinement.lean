/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q86
-/
module

public import Mathlib.Topology.LocallyClosed
public import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Irreducible

/-!
# Finite good refinements of Noetherian locally closed partitions

Source: Stacks Project, Topology, Tag 09Y5,
`lemma-noetherian-partition-refined-by-stratification`, and Tag 09Y0,
`definition-good-stratification`
(blueprint: lem-sfb-noetherian-good-stratification-refinement).
-/

@[expose] public section

universe u v

namespace Topology

open Set TopologicalSpace in
private theorem exists_open_piece
    {X : Type u} [TopologicalSpace X] [NoetherianSpace X] [Nonempty X]
    {A : Type v} [Finite A] (P : A → Set X)
    (hl : ∀ a, IsLocallyClosed (P a)) (hc : (⋃ a, P a) = univ) :
    ∃ U : Set X, IsOpen U ∧ U.Nonempty ∧ ∃ a, U ⊆ P a := by
  classical
  let x : X := Classical.choice inferInstance
  let Z := irreducibleComponent x
  have hZ : Z ∈ irreducibleComponents X := irreducibleComponent_mem_irreducibleComponents x
  obtain ⟨O, hO, hOne, hOZ⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent Z hZ
  let S : Finset (Set X) := (Set.finite_range fun a ↦ closure (P a)).toFinset
  have hcover : Z ⊆ ⋃₀ (S : Set (Set X)) := by
    intro y hy
    obtain ⟨a, ha⟩ := mem_iUnion.mp (hc ▸ mem_univ y)
    exact mem_sUnion.mpr ⟨closure (P a), by simp [S], subset_closure ha⟩
  obtain ⟨D, hDS, hZD⟩ := isIrreducible_iff_sUnion_isClosed.mp hZ.1 S
    (by
      intro D hD
      obtain ⟨a, rfl⟩ : ∃ a, closure (P a) = D := by simpa [S] using hD
      exact isClosed_closure) hcover
  obtain ⟨a, ha⟩ : ∃ a, closure (P a) = D := by simpa [S] using hDS
  rw [← ha] at hZD
  obtain ⟨V, C, hV, hC, heq⟩ := hl a
  have hZC : Z ⊆ C := (hZD.trans (closure_minimal (heq ▸ inter_subset_right) hC))
  have hmeet : (O ∩ P a).Nonempty := by
    obtain ⟨y, hy⟩ := hOne
    exact (mem_closure_iff.mp (hZD (hOZ hy))) O hO hy
  refine ⟨O ∩ V, hO.inter hV, ?_, a, ?_⟩
  · obtain ⟨y, hyO, hyP⟩ := hmeet
    exact ⟨y, hyO, (heq ▸ hyP).1⟩
  · intro y hy
    rw [heq]
    exact ⟨hy.2, hZC (hOZ hy.1)⟩

open Set TopologicalSpace in
private theorem exists_closed_refinement
    {T : Type u} [TopologicalSpace T] [NoetherianSpace T] (S : Closeds T) :
    ∀ {A : Type v} [Finite A] (P : A → Set T),
      (∀ a, IsLocallyClosed (P a)) → (⋃ a, P a) = (S : Set T) →
      Pairwise (fun a a' ↦ Disjoint (P a) (P a')) →
      ∃ (n : ℕ) (Q : Fin n → Set T),
        (∀ b, (Q b).Nonempty) ∧ (∀ b, IsLocallyClosed (Q b)) ∧
        (⋃ b, Q b) = (S : Set T) ∧ Pairwise (fun b c ↦ Disjoint (Q b) (Q c)) ∧
        (∀ b, ∃ a, Q b ⊆ P a) ∧
        (∀ b c, (Q b ∩ closure (Q c)).Nonempty → Q b ⊆ closure (Q c)) := by
  classical
  apply (wellFounded_lt (α := Closeds T)).induction S
  intro S ih A _ P hl hc hd
  by_cases hS : (S : Set T) = ∅
  · refine ⟨0, Fin.elim0, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro b; exact Fin.elim0 b
    · intro b; exact Fin.elim0 b
    · simpa using hS.symm
    · intro b; exact Fin.elim0 b
    · intro b; exact Fin.elim0 b
    · intro b; exact Fin.elim0 b
  have hSne : (S : Set T).Nonempty := Set.nonempty_iff_ne_empty.mpr hS
  have : Nonempty (S : Set T) := hSne.to_subtype
  have : NoetherianSpace (S : Set T) :=
    (noetherianSpace_set_iff _).mpr (fun t _ ↦ NoetherianSpace.isCompact t)
  obtain ⟨W, hW, hWne, a, hWa⟩ := exists_open_piece
    (fun a ↦ (Subtype.val : S → T) ⁻¹' P a)
    (fun a ↦ (hl a).preimage continuous_subtype_val) (by
      ext x
      simp only [mem_iUnion, mem_preimage, mem_univ, iff_true]
      exact mem_iUnion.mp (hc.symm ▸ x.property))
  obtain ⟨V, hV, hVW⟩ := isOpen_induced_iff.mp hW
  let U : Set T := V ∩ (S : Set T)
  have hUne : U.Nonempty := by
    obtain ⟨x, hx⟩ := hWne
    exact ⟨x.val, (congrArg (fun B ↦ x ∈ B) hVW).mpr hx, x.property⟩
  have hUa : U ⊆ P a := by
    intro x hx
    exact hWa ((congrArg (fun B ↦ (⟨x, hx.2⟩ : S) ∈ B) hVW).mp hx.1)
  have hUl : IsLocallyClosed U := ⟨V, S, hV, S.isClosed, rfl⟩
  let C : Closeds T := ⟨(S : Set T) ∩ Vᶜ, S.isClosed.inter hV.isClosed_compl⟩
  have hCS : C < S := by
    refine lt_iff_le_not_ge.mpr ⟨inter_subset_left, ?_⟩
    intro h
    obtain ⟨x, hxV, hxS⟩ := hUne
    exact (h hxS).2 hxV
  let R : A × Bool → Set T := fun k ↦
    if k.2 then P k.1 ∩ (C : Set T) ∩ closure U
    else P k.1 ∩ (C : Set T) ∩ (closure U)ᶜ
  have hRl : ∀ k, IsLocallyClosed (R k) := by
    rintro ⟨a, b⟩
    cases b
    · exact ((hl a).inter C.isClosed.isLocallyClosed).inter
        isClosed_closure.isOpen_compl.isLocallyClosed
    · exact ((hl a).inter C.isClosed.isLocallyClosed).inter
        isClosed_closure.isLocallyClosed
  have hRc : (⋃ k, R k) = (C : Set T) := by
    ext x
    constructor
    · rintro hx
      obtain ⟨⟨a, b⟩, hx⟩ := mem_iUnion.mp hx
      cases b <;> exact hx.1.2
    · intro hx
      obtain ⟨a, ha⟩ := mem_iUnion.mp (hc ▸ hx.1)
      by_cases hxu : x ∈ closure U
      · exact mem_iUnion.mpr ⟨(a, true), ⟨ha, hx⟩, hxu⟩
      · exact mem_iUnion.mpr ⟨(a, false), ⟨ha, hx⟩, hxu⟩
  have hRd : Pairwise (fun k l ↦ Disjoint (R k) (R l)) := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ hne
    apply Set.disjoint_left.mpr
    intro x hx hy
    by_cases haa : a = a'
    · subst a'
      cases b <;> cases b' <;> simp_all [R]
    · have hpa : x ∈ P a := by cases b <;> exact hx.1.1
      have hpa' : x ∈ P a' := by cases b' <;> exact hy.1.1
      exact Set.disjoint_left.mp (hd haa) hpa hpa'
  obtain ⟨n, Q, hQne, hQl, hQc, hQd, hQr, hQg⟩ := ih C hCS R hRl hRc hRd
  have hQsub (b : Fin n) : Q b ⊆ (C : Set T) := by
    intro x hx
    rw [← hQc]
    exact mem_iUnion.mpr ⟨b, hx⟩
  have hQcl (b : Fin n) : closure (Q b) ⊆ (C : Set T) :=
    closure_minimal (hQsub b) C.isClosed
  have hUQ (b : Fin n) : Disjoint U (Q b) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact (hQsub b hy).2 hx.1
  let Q' : Fin (n + 1) → Set T := Fin.cases U Q
  refine ⟨n + 1, Q', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Fin.cases hUne hQne
  · exact Fin.cases hUl hQl
  · ext x
    constructor
    · intro hx
      obtain ⟨b, hb⟩ := mem_iUnion.mp hx
      cases b using Fin.cases with
      | zero => exact hb.2
      | succ b => exact (hQsub b hb).1
    · intro hx
      by_cases hxV : x ∈ V
      · exact mem_iUnion.mpr ⟨0, hxV, hx⟩
      · obtain ⟨b, hb⟩ := mem_iUnion.mp (hQc ▸ (show x ∈ (C : Set T) from ⟨hx, hxV⟩))
        exact mem_iUnion.mpr ⟨b.succ, hb⟩
  · intro b c hbc
    cases b using Fin.cases with
    | zero =>
      cases c using Fin.cases with
      | zero => exact (hbc rfl).elim
      | succ c => exact hUQ c
    | succ b =>
      cases c using Fin.cases with
      | zero => exact (hUQ b).symm
      | succ c => exact hQd (fun h ↦ hbc (congrArg Fin.succ h))
  · intro b
    cases b using Fin.cases with
    | zero => exact ⟨a, hUa⟩
    | succ b =>
      obtain ⟨⟨a, k⟩, hk⟩ := hQr b
      refine ⟨a, ?_⟩
      cases k <;> exact fun x hx ↦ (hk hx).1.1
  · intro b c hmeet
    cases b using Fin.cases with
    | zero =>
      cases c using Fin.cases with
      | zero => exact subset_closure
      | succ c =>
        obtain ⟨x, hxU, hxQ⟩ := hmeet
        exact ((hQcl c hxQ).2 hxU.1).elim
    | succ b =>
      cases c using Fin.cases with
      | zero =>
        obtain ⟨⟨a, k⟩, hk⟩ := hQr b
        cases k
        · obtain ⟨x, hxQ, hxU⟩ := hmeet
          exact ((hk hxQ).2 hxU).elim
        · exact fun x hx ↦ (hk hx).2
      | succ c => exact hQg b c hmeet

/-- A finite locally closed partition of a Noetherian space has a finite good refinement
with nonempty strata. The last clause explicitly expresses that every stratum closure is
a union of strata. When the space is empty, `n = 0` is allowed.

Source: Stacks Project, Topology, Tag 09Y5,
`lemma-noetherian-partition-refined-by-stratification`, and Tag 09Y0,
`definition-good-stratification`
(blueprint: lem-sfb-noetherian-good-stratification-refinement).

Proof:
1. Use the descending-chain condition to induct on closed subspaces, proving the assertion
   for every finite locally closed partition of each such subspace simultaneously. Closed
   subspaces inherit the condition. The empty subspace has the empty refinement.
2. In a nonempty subspace, rename it `T`. By
   `lem-sc-noetherian-finite-irreducible-components` and
   `lem-sc-irreducible-components-cover`, its distinct irreducible components form a finite
   nonempty closed cover. Their maximal irreducibility is
   `def-weil-irreducible-components`.
3. Choose a component `Z`, and let `O` be the complement of the other components. It is an
   open subset contained in `Z`, nonempty by irreducibility and maximality of components.
   The finitely many closed sets `closure (P a)` cover `T`, so irreducibility puts `Z` inside
   one of them. Write that `P a` as `V ∩ D`, with `V` open and `D` closed, using
   `def-weil-locally-closed-subset`. Then `Z ⊆ D`. The nonempty open `O` meets `P a`, since
   `O ⊆ Z ⊆ closure (P a)`. Thus `U = O ∩ V = O ∩ P a` is a nonempty open of `T` contained
   in this original part.
4. Put `C = T ∖ U` and `H = closure U ∖ U`. For every original part form
   `P a ∩ C ∩ closure U` and `P a ∩ C ∩ (closure U)ᶜ`, and discard empty pieces. They form a
   finite locally closed partition of the proper closed subspace `C`, refining the original
   partition and adapted to `H`: each piece lies in `H` or outside `closure U`.
5. Apply induction to this partition of `C`. Its refined parts are locally closed in `T`:
   an open of `C` is `C ∩ V` for an ambient open `V`, and a closed of the closed subspace
   `C` is ambient closed. Their ambient closures lie in `C` and agree with their subspace
   closures, so the good-stratification condition still holds for every pair of these parts.
6. Adjoin `U`. The old closures are contained in `C`, hence do not meet `U`. Each old part
   either lies in `H ⊆ closure U` or avoids `closure U`, so meeting `closure U` implies
   containment. The pair `(U, U)` satisfies containment automatically. These are all pairs;
   finiteness, nonemptiness, disjointness, local closedness and refinement are preserved.
   Every point of a stratum closure lies in a unique part of the partition; goodness puts
   that whole part inside the closure. Taking those parts gives the last union equality.
-/
theorem exists_finite_good_stratification_refinement
    {T : Type u} [TopologicalSpace T] [TopologicalSpace.NoetherianSpace T]
    {A : Type v} [Finite A] (P : A → Set T)
    (hP_locallyClosed : ∀ a : A, IsLocallyClosed (P a))
    (hP_cover : (⋃ a : A, P a) = Set.univ)
    (hP_disjoint : Pairwise (fun a a' : A ↦ Disjoint (P a) (P a'))) :
    ∃ (n : ℕ) (Q : Fin n → Set T),
      (∀ b : Fin n, (Q b).Nonempty) ∧
      (∀ b : Fin n, IsLocallyClosed (Q b)) ∧
      (⋃ b : Fin n, Q b) = Set.univ ∧
      Pairwise (fun b c : Fin n ↦ Disjoint (Q b) (Q c)) ∧
      (∀ b : Fin n, ∃ a : A, Q b ⊆ P a) ∧
      (∀ b c : Fin n, (Q b ∩ closure (Q c)).Nonempty → Q b ⊆ closure (Q c)) ∧
      (∀ c : Fin n, ∃ I : Set (Fin n), closure (Q c) = ⋃ b ∈ I, Q b) := by
  classical
  obtain ⟨n, Q, hne, hl, hc, hd, hr, hg⟩ :=
    exists_closed_refinement (⊤ : TopologicalSpace.Closeds T) P
      hP_locallyClosed hP_cover hP_disjoint
  have hcover : (⋃ b, Q b) = (Set.univ : Set T) := hc
  refine ⟨n, Q, hne, hl, hcover, hd, hr, hg, ?_⟩
  intro c
  refine ⟨{b | Q b ⊆ closure (Q c)}, ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨b, hb⟩ := Set.mem_iUnion.mp (hcover.symm ▸ Set.mem_univ x)
    exact Set.mem_iUnion₂.mpr ⟨b, hg b c ⟨x, hb, hx⟩, hb⟩
  · intro hx
    obtain ⟨b, hb, hxb⟩ := Set.mem_iUnion₂.mp hx
    exact hb hxb

end Topology
