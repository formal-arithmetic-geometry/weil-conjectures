/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Finiteness.Defs

/-!
# Reduction of polynomial action coefficients to the base ring

Source: Stacks Project, Algebra, Tag 0561, proof of
`lemma-finitely-presented-over-subring`, the degree-lowering paragraph
(blueprint: lem-trf-polynomial-action-reduction).
-/

@[expose] public section

universe u v w

open scoped BigOperators

namespace Module

/-- Stacks Project, Algebra, Tag 0561, the paragraph beginning with an expression
`z = ∑ b_j y_j` (blueprint: lem-trf-polynomial-action-reduction).
If algebra generators act on specified module generators by matrices over the base ring,
then every module element is a base-ring linear combination of those same generators.

Proof: first write an element as an `S`-linear combination of the `e j`, using
`def-weil-finitely-generated-module`. The algebra generation hypothesis, in the sense of
`def-weil-pbc-finite-type-algebra`, writes every coefficient as a polynomial in the `x i`
with coefficients in `R`. Induct simultaneously for all `j` on the total degree of a
monomial to show that its action on `e j` is an `R`-linear combination of the `e k`.
The degree-zero case is `e j` itself. At positive degree, remove one factor `x i`, use
the displayed action relation, and apply the induction hypothesis to each remaining
monomial acting on `e k`. The scalar-tower identity commutes the `R` coefficients
past this action. Substitute these expressions into the initial finite sum and collect
the coefficient of each `e k`. The same calculation covers both empty generating
families and the zero ring. -/
theorem exists_eq_sum_smul_of_polynomial_action
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
    {N : Type w} [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    {n m : ℕ} (x : Fin n → S) (e : Fin m → N)
    (hx : Algebra.adjoin R (Set.range x) = ⊤)
    (he : Submodule.span S (Set.range e) = ⊤)
    (a : Fin n → Fin m → Fin m → R)
    (ha : ∀ (i : Fin n) (j : Fin m), x i • e j = ∑ k : Fin m, a i j k • e k) :
    ∀ z : N, ∃ c : Fin m → R, z = ∑ k : Fin m, c k • e k := by
  let P := Submodule.span R (Set.range e)
  have heP (j : Fin m) : e j ∈ P := Submodule.subset_span ⟨j, rfl⟩
  have hgen (i : Fin n) (v : N) (hv : v ∈ P) : x i • v ∈ P := by
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hv
    rw [Finset.smul_sum]
    apply P.sum_mem
    intro j _
    rw [smul_comm, ha i j]
    exact P.smul_mem _ (P.sum_mem fun k _ ↦ P.smul_mem _ (heP k))
  have hstable (s : S) : ∀ v ∈ P, s • v ∈ P := by
    have hs : s ∈ Algebra.adjoin R (Set.range x) := by rw [hx]; trivial
    induction hs using Algebra.adjoin_induction with
    | mem s hs =>
      obtain ⟨i, rfl⟩ := hs
      exact hgen i
    | algebraMap r =>
      intro v hv
      simpa only [IsScalarTower.algebraMap_smul] using P.smul_mem r hv
    | add s t _ _ hs ht =>
      intro v hv
      rw [add_smul]
      exact P.add_mem (hs v hv) (ht v hv)
    | mul s t _ _ hs ht =>
      intro v hv
      rw [mul_smul]
      exact hs _ (ht v hv)
  intro z
  have hz : z ∈ Submodule.span S (Set.range e) := by rw [he]; trivial
  have hzP : z ∈ P := by
    induction hz using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨j, rfl⟩ := hv
      exact heP j
    | zero => exact P.zero_mem
    | add v w _ _ hv hw => exact P.add_mem hv hw
    | smul s v _ hv => exact hstable s v hv
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hzP
  exact ⟨c, hc.symm⟩

end Module
