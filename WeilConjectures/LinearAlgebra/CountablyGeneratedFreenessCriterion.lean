/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Data.Set.Countable
public import Mathlib.LinearAlgebra.FreeModule.Basic

import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# A freeness criterion for countably generated modules

Source: Stacks Project, Algebra, Tag 0591, `lemma-freeness-criteria`
(blueprint: lem-trf-countably-generated-freeness-criterion).
-/

@[expose] public section

universe u v

namespace Module

private theorem finite_basis_of_finite_independent
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    {s : Set M} (hs : s.Finite) (hli : LinearIndepOn R id s) :
    ∃ n : ℕ, Nonempty (Basis (Fin n) R (Submodule.span R s)) := by
  classical
  let := hs.fintype
  have b : Basis s R (Submodule.span R s) := by
    let b := Basis.span hli
    change Basis s R (Submodule.span R (Set.range ((↑) : s → M))) at b
    rw [Subtype.range_coe] at b
    exact b
  exact ⟨Fintype.card s, ⟨b.reindex (Fintype.equivFin s)⟩⟩

private theorem isCompl_sup_map
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    {F N : Submodule R M} (hFN : IsCompl F N)
    {P Q : Submodule R N} (hPQ : IsCompl P Q) :
    IsCompl (F ⊔ P.map N.subtype) (Q.map N.subtype) := by
  have he : P.map N.subtype ⊔ Q.map N.subtype = N := by
    rw [← Submodule.map_sup, hPQ.sup_eq_top, Submodule.map_top, Submodule.range_subtype]
  apply Disjoint.isCompl_sup_left_of_isCompl_sup_right
    (Submodule.disjoint_map (Submodule.injective_subtype N) hPQ.disjoint)
  rwa [he]

private theorem exists_finite_split_span
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Free R M] (x : M) :
    ∃ (s : Set M) (H : Submodule R M), s.Finite ∧ LinearIndepOn R id s ∧
      IsCompl (Submodule.span R s) H ∧ x ∈ Submodule.span R s := by
  classical
  let b := Free.chooseBasis R M
  let t : Set (Free.ChooseBasisIndex R M) := (b.repr x).support
  refine ⟨b '' t, Submodule.span R (b '' tᶜ), ?_, ?_, ?_, ?_⟩
  · exact (Finset.finite_toSet _).image b
  · exact (b.linearIndependent.linearIndepOn t).id_image
  · exact b.linearIndependent.isCompl_span_image b.span_eq isCompl_compl
  · exact b.mem_span_repr_support x

private theorem extend_finite_split_independent
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (hsummands : ∀ (N F : Submodule R M), IsCompl N F →
      (∃ n : ℕ, Nonempty (Basis (Fin n) R F)) →
      ∀ x : N, ∃ G H : Submodule R N, IsCompl G H ∧ x ∈ G ∧ Free R G)
    {s : Set M} (hs : s.Finite) (hli : LinearIndepOn R id s)
    (hcomp : ∃ N : Submodule R M, IsCompl (Submodule.span R s) N) (x : M) :
    ∃ t : Set M, s ⊆ t ∧ t.Finite ∧ LinearIndepOn R id t ∧
      (∃ N : Submodule R M, IsCompl (Submodule.span R t) N) ∧
      x ∈ Submodule.span R t := by
  classical
  obtain ⟨N, hFN⟩ := hcomp
  let y := N.projectionOnto (Submodule.span R s) hFN.symm x
  obtain ⟨G, H, hGH, hyG, hG⟩ :=
    hsummands N _ hFN.symm (finite_basis_of_finite_independent hs hli) y
  let := hG
  obtain ⟨a, Q, ha, hliA, hAQ, hyA⟩ := exists_finite_split_span (R := R) (⟨y, hyG⟩ : G)
  let P := Submodule.span R a
  have hPQ : IsCompl (P.map G.subtype) (Q.map G.subtype ⊔ H) := by
    have he : P.map G.subtype ⊔ Q.map G.subtype = G := by
      rw [← Submodule.map_sup, hAQ.sup_eq_top, Submodule.map_top, Submodule.range_subtype]
    apply Disjoint.isCompl_sup_right_of_isCompl_sup_left
      (Submodule.disjoint_map (Submodule.injective_subtype G) hAQ.disjoint)
    rwa [he]
  let f : G →ₗ[R] M := N.subtype.comp G.subtype
  let t : Set M := f '' a
  have htspan : Submodule.span R t = (P.map G.subtype).map N.subtype := by
    rw [← Submodule.map_comp, ← Submodule.span_image]
  have htN : Submodule.span R t ≤ N := by
    rw [htspan]
    exact Submodule.map_subtype_le _ _
  have hliT : LinearIndepOn R id t := by
    exact hliA.id_imageₛ (fun _ _ _ _ h ↦
      Subtype.ext (Subtype.ext h))
  refine ⟨s ∪ t, Set.subset_union_left, hs.union (ha.image f),
    hli.id_union hliT (hFN.disjoint.mono_right htN), ?_, ?_⟩
  · refine ⟨(Q.map G.subtype ⊔ H).map N.subtype, ?_⟩
    rw [Submodule.span_union, htspan]
    exact isCompl_sup_map hFN hPQ
  · have hy : (y : M) ∈ Submodule.span R t := by
      rw [htspan]
      exact Submodule.mem_map.mpr ⟨y,
        Submodule.mem_map.mpr ⟨⟨y, hyG⟩, hyA, rfl⟩, rfl⟩
    have hx := Submodule.projection_add_projection_eq_self hFN.symm x
    rw [← hx, Submodule.span_union]
    exact Submodule.add_mem _ (Submodule.mem_sup_right hy)
      (Submodule.mem_sup_left (Submodule.coe_mem _))

/-- A countably generated module is free if each element of every complement of a finite
free summand belongs to a free direct summand of that complement.

Source: Stacks Project, Algebra, Tag 0591, `lemma-freeness-criteria`
(blueprint: lem-trf-countably-generated-freeness-criterion).

Proof:
1. Enumerate the countable generating subset as a sequence, repeating elements or inserting
   zero when the subset is finite or empty. Each element is a finite linear combination of
   terms of this sequence.
2. Inductively construct finite free summands `F₁, ..., Fₙ` whose sum `Sₙ` is a direct summand
   of `M` containing the first `n` generators. The union of their finite bases is a finite
   basis of `Sₙ` (def-weil-pbc-free-module). Split `M` as `N ⊕ Sₙ` and project the next
   generator to `N`. The hypothesis puts this component in a free direct summand `G` of `N`.
3. Choose a basis of `G`. Only finitely many basis vectors occur in this component, so their
   span is finite free and has the span of the remaining basis vectors as a complement in
   `G` (def-weil-pbc-free-module). Use it as `Fₙ₊₁`; composing the splittings gives `Sₙ₊₁`
   as a direct summand containing the first `n + 1` generators.
4. Every element of `M` lies in some `Sₙ`, since it involves only finitely many generators.
   Each finite relation lies in one finite-stage direct sum, so its components vanish.
   Thus `M` is the direct sum of the `Fᵢ`.
5. The disjoint union of their finite bases is a basis of that direct sum: finite support
   gives spanning, and coordinatewise uniqueness gives independence
   (def-weil-pbc-free-module). Hence `M` is free. -/
theorem free_of_countable_generators_of_free_summands
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (hcountable : ∃ s : Set M, s.Countable ∧ Submodule.span R s = ⊤)
    (hsummands : ∀ (N F : Submodule R M), IsCompl N F →
      (∃ n : ℕ, Nonempty (Module.Basis (Fin n) R F)) →
      ∀ x : N, ∃ G H : Submodule R N, IsCompl G H ∧ x ∈ G ∧ Module.Free R G) :
    Module.Free R M := by
  classical
  obtain ⟨s, hs, hspan⟩ := hcountable
  let x : ℕ → M := Set.enumerateCountable hs 0
  let Good : Set M → Prop := fun t ↦ t.Finite ∧ LinearIndepOn R id t ∧
    ∃ N : Submodule R M, IsCompl (Submodule.span R t) N
  have hstep (t : Set M) (ht : Good t) (n : ℕ) :
      ∃ t' : Set M, t ⊆ t' ∧ Good t' ∧ x n ∈ Submodule.span R t' := by
    obtain ⟨t', hsub, hfin, hli, hc, hx⟩ :=
      extend_finite_split_independent hsummands ht.1 ht.2.1 ht.2.2 (x n)
    exact ⟨t', hsub, ⟨hfin, hli, hc⟩, hx⟩
  let next (n : ℕ) (t : {t : Set M // Good t}) : {t : Set M // Good t} :=
    ⟨(hstep t.1 t.2 n).choose, (hstep t.1 t.2 n).choose_spec.2.1⟩
  have hempty : Good ∅ := by
    refine ⟨Set.finite_empty, linearIndepOn_empty R id, ⊤, ?_⟩
    simpa only [Submodule.span_empty] using (isCompl_bot_top : IsCompl (⊥ : Submodule R M) ⊤)
  let seq : ℕ → {t : Set M // Good t} :=
    fun n ↦ Nat.rec ⟨∅, hempty⟩ (fun n t ↦ next n t) n
  have hmono : Monotone (fun n ↦ (seq n).1) := by
    apply monotone_nat_of_le_succ
    intro n
    exact (hstep (seq n).1 (seq n).2 n).choose_spec.1
  have hx (n : ℕ) : x n ∈ Submodule.span R (seq (n + 1)).1 :=
    (hstep (seq n).1 (seq n).2 n).choose_spec.2.2
  let B : Set M := ⋃ n, (seq n).1
  have hli : LinearIndepOn R id B :=
    linearIndepOn_iUnion_of_directed hmono.directed_le (fun n ↦ (seq n).2.2.1)
  apply Free.of_basis (Basis.mk hli ?_)
  have hsB : s ⊆ Submodule.span R B := by
    intro y hy
    obtain ⟨n, rfl⟩ := Set.subset_range_enumerate hs 0 hy
    exact Submodule.span_mono (Set.subset_iUnion (fun n ↦ (seq n).1) (n + 1)) (hx n)
  simpa only [id_eq, Subtype.range_coe] using
    (hspan ▸ (Submodule.span_le.mpr hsB))

end Module
