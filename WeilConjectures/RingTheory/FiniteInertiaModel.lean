/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.RingTheory.Ideal.Pointwise
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
/-!
# A finite subalgebra detecting inertia

Source: Stacks Project, Tag 0BST, finite reduction of the equivariant idempotent construction
(blueprint: lem-dl-a1-finite-inertia-model).
-/

@[expose] public section
set_option autoImplicit false
universe u v

/-- There is a finite stable subalgebra on which the original inertia is detected.
Source: Stacks Project, Tag 0BST, finite reduction using integral orbit generators.
(blueprint: lem-dl-a1-finite-inertia-model).

Proof: for each group element outside inertia choose an element witnessing its failure to
act trivially modulo q. Adjoin every group translate of these finitely many witnesses.
The generators are integral because R is an invariant extension of C, so the resulting
subalgebra is module-finite. Its stability follows by induction on algebra expressions:
translation permutes the generators and fixes the base. Each original witness belongs to
the subalgebra, so acting trivially on the subalgebra modulo q forces membership in the
original inertia. The argument also works for the unit ideal and for a trivial action. -/
theorem Ideal.exists_finite_inertia_model
    (C R : Type u) [CommRing C] [CommRing R] [Algebra C R]
    (G : Type v) [Group G] [Finite G] [MulSemiringAction G R]
    [SMulCommClass G C R] [Algebra.IsInvariant C R G]
    (q : Ideal R) :
    ∃ D : Subalgebra C R, Module.Finite C D ∧
      (∀ (g : G) (x : R), x ∈ D → g • x ∈ D) ∧
      (∀ g : G, (∀ x : D, g • (x : R) - (x : R) ∈ q) → g ∈ q.inertia G) := by
  classical
  have : Algebra.IsIntegral C R := Algebra.IsInvariant.isIntegral C R G
  have hw : ∀ g : G, ∃ x : R, g ∉ q.inertia G → g • x - x ∉ q := by
    intro g
    by_cases hg : g ∈ q.inertia G
    · exact ⟨0, fun hn ↦ False.elim (hn hg)⟩
    · have hg' : ¬ ∀ x : R, g • x - x ∈ q := hg
      obtain ⟨x, hx⟩ := not_forall.mp hg'
      exact ⟨x, fun _ ↦ hx⟩
  choose w hw using hw
  let T : Set R := Set.range (fun gh : G × G ↦ gh.1 • w gh.2)
  let D := Algebra.adjoin C T
  refine ⟨D, Algebra.finite_adjoin_of_finite_of_isIntegral (Set.finite_range _)
    (fun x _ ↦ Algebra.IsIntegral.isIntegral x), ?_, ?_⟩
  · intro g x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨⟨h, k⟩, rfl⟩ := hx
      apply Algebra.subset_adjoin
      exact ⟨(g * h, k), mul_smul g h (w k)⟩
    | algebraMap c =>
      rw [smul_algebraMap]
      exact D.algebraMap_mem c
    | add x y hx hy hx' hy' =>
      rw [smul_add]
      exact D.add_mem hx' hy'
    | mul x y hx hy hx' hy' =>
      rw [smul_mul']
      exact D.mul_mem hx' hy'
  · intro g hg
    by_contra hnot
    apply hw g hnot
    have hwD : w g ∈ D := Algebra.subset_adjoin
      ⟨(1, g), one_smul G (w g)⟩
    exact hg ⟨w g, hwD⟩
