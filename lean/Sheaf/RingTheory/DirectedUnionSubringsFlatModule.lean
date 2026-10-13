/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.Data.Finset.Order

/-! # Flat modules over directed unions of subrings

Source: literature/stacks-project/algebra.tex, Lemma Tag 05UU (blueprint:
lem-weil-pbc-directed-union-subrings-flat-module)
-/

@[expose] public section

universe u v w x

namespace RingTheory

-- The existing Mstage binder names an unused index; keep its signature unchanged.
set_option linter.unusedVariables false in
/-- A module colimit over a directed union of subrings is flat when every stage
is flat. Source: Stacks Project, Algebra, Lemma Tag 05UU, part (2),
and the equational criterion, Lemma Tag 00HK
(blueprint: lem-weil-pbc-directed-union-subrings-flat-module).

Proof (equational criterion, Stacks Tag 00HK):
1. Start with a finite relation `∑ k, r k • m k = 0`. Choose a stage containing
   each coefficient, and a stage representative for each module element using
   `h_repr`. Directedness gives a common upper bound, also for the empty relation
   since the index type is nonempty. Move all coefficients and representatives
   there. Naturality identifies their images with the original module elements.
2. The sum of the lifted relation maps to zero under `ι`. By `h_zero`, its image
   under a transition to some later stage is zero. Linearity of that transition
   identifies this with the relation whose coefficients and module elements have
   both been moved to the later stage.
3. Stage flatness and the forward equational criterion give a finite coefficient
   matrix and module elements trivializing this relation. Map the matrix into `R`
   by the subring inclusion and the module elements into `M` by `ι`. Linearity of
   `ι` gives the required expansions of the original elements; the subring map
   takes the zero coefficient equations to zero. The backward equational criterion
   now proves flatness. No categorical colimit or tensor comparison is needed. -/
theorem directedUnionSubrings_flat_module
    {R : Type u} [CommRing R]
    {Λ : Type v} [PartialOrder Λ] [Nonempty Λ]
    [IsDirected Λ (· ≤ ·)]
    (Rsub : Λ → Subring R)
    (hR : ∀ {i j : Λ}, i ≤ j → Rsub i ≤ Rsub j)
    (hUnion : (Set.univ : Set R) = ⋃ i, (Rsub i : Set R))
    {M : Type w} [AddCommMonoid M] [Module R M]
    (Mstage : ∀ i : Λ, Type x)
    (instAdd : ∀ i : Λ, AddCommMonoid (Mstage i))
    (instMod : ∀ i : Λ, Module (Rsub i) (Mstage i))
    (ι : ∀ i : Λ,
      letI : Module (Rsub i) M := Module.compHom M (Rsub i).subtype
      Mstage i →ₗ[Rsub i] M)
    (t : ∀ {i j : Λ} (h : i ≤ j),
      letI : Module (Rsub i) (Mstage j) :=
        Module.compHom (Mstage j) (Subring.inclusion (hR h))
      Mstage i →ₗ[Rsub i] Mstage j)
    (t_id : ∀ (i : Λ) (x : Mstage i), t (le_refl i) x = x)
    (t_comp : ∀ {i j k : Λ} (h₁ : i ≤ j) (h₂ : j ≤ k) (x : Mstage i),
      t h₂ (t h₁ x) = t (h₁.trans h₂) x)
    (ι_naturality : ∀ {i j : Λ} (h : i ≤ j) (x : Mstage i),
      ι j (t h x) = ι i x)
    (h_repr : ∀ m : M, ∃ (i : Λ) (x : Mstage i), ι i x = m)
    (h_zero : ∀ {i : Λ} (x : Mstage i), ι i x = 0 →
      ∃ j : Λ, ∃ h : i ≤ j, t h x = 0)
    (hflat : ∀ i : Λ, Module.Flat (Rsub i) (Mstage i)) :
    Module.Flat R M := by
  classical
  clear t_id t_comp
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup R
  let : ∀ i, AddCommGroup (Mstage i) :=
    fun i => Module.addCommMonoidToAddCommGroup (Rsub i)
  let : ∀ i, Module (Rsub i) M := fun i => Module.compHom M (Rsub i).subtype
  refine Module.Flat.of_forall_isTrivialRelation fun {n r m} hm => ?_
  have hr (k : Fin n) : ∃ i, r k ∈ Rsub i := by
    have : r k ∈ ⋃ i, (Rsub i : Set R) := by rw [← hUnion]; trivial
    exact Set.mem_iUnion.mp this
  choose ir hir using hr
  choose im x hx using fun k : Fin n => h_repr (m k)
  obtain ⟨i, hi⟩ := ((Finset.univ.image ir) ∪ (Finset.univ.image im)).exists_le
  have hri (k : Fin n) : ir k ≤ i :=
    hi _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ k)))
  have hmi (k : Fin n) : im k ≤ i :=
    hi _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ k)))
  let a (k : Fin n) : Rsub i := ⟨r k, hR (hri k) (hir k)⟩
  let y (k : Fin n) : Mstage i := t (hmi k) (x k)
  have hy (k : Fin n) : ι i (y k) = m k :=
    (ι_naturality (hmi k) (x k)).trans (hx k)
  have hz : ι i (∑ k, a k • y k) = 0 := by
    rw [map_sum]
    simp only [map_smul, hy]
    exact hm
  obtain ⟨j, hij, hzj⟩ := h_zero _ hz
  let b (k : Fin n) : Rsub j := Subring.inclusion (hR hij) (a k)
  let z (k : Fin n) : Mstage j := t hij (y k)
  have hrel : ∑ k, b k • z k = 0 := by
    rw [map_sum] at hzj
    simp only [map_smul] at hzj
    exact hzj
  have : Module.Flat (Rsub j) (Mstage j) := hflat j
  obtain ⟨l, c, q, hzq, hc⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel
  refine ⟨l, fun k s => (c k s : R), fun s => ι j (q s), ?_, ?_⟩
  · intro k
    calc
      m k = ι j (z k) := ((ι_naturality hij (y k)).trans (hy k)).symm
      _ = ι j (∑ s, c k s • q s) := congrArg (ι j) (hzq k)
      _ = ∑ s, (c k s : R) • ι j (q s) := by
        simp only [map_sum, map_smul]
        rfl
  · intro s
    have he := congrArg (Rsub j).subtype (hc s)
    simpa only [map_sum, map_mul, map_zero, b, a, Subring.coe_subtype,
      Subring.coe_inclusion] using he

end RingTheory
