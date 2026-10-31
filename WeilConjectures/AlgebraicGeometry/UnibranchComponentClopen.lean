/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.Irreducible
import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Clopen irreducible components under local finiteness and uniqueness

Source: Stacks Project, more-morphisms.tex, Tag 0GS9, proof of the final
sentence asserting that the component is open and closed (blueprint:
lem-dl-a1-unibranch-component-clopen).

## Main statements

* `AlgebraicGeometry.unibranch_component_clopen` states that finite local
  component spaces with at most one component through each point have clopen
  irreducible components.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry

/-- Every irreducible component is clopen when compact opens have finitely many
components and each point lies on at most one component.

Source: Stacks Project, more-morphisms.tex, Tag 0GS9, proof of the final
sentence asserting that the component is open and closed (blueprint:
lem-dl-a1-unibranch-component-clopen).

Proof plan:
1. For a point of a component, choose an affine quasi-compact open neighbourhood.
2. Remove the finitely many irreducible components of that neighbourhood that do
   not contain the point. The remaining open neighbourhood lies in the chosen
   component by the uniqueness hypothesis and the component-cover property.
3. Thus every component is open; it is closed by the definition of irreducible
   components.
-/
theorem unibranch_component_clopen
    (U : Scheme.{u})
    (hfinite : ∀ (V : Set U), IsOpen V → IsCompact V →
      (irreducibleComponents V).Finite)
    (hunique : ∀ (x : U) {C₁ C₂ : Set U},
      C₁ ∈ irreducibleComponents U → C₂ ∈ irreducibleComponents U →
        x ∈ C₁ → x ∈ C₂ → C₁ = C₂) :
    ∀ (C : Set U), C ∈ irreducibleComponents U → IsClopen C := by
  classical
  intro C hC
  have hclosed : IsClosed C := isClosed_of_mem_irreducibleComponents C hC
  have hopen : IsOpen C := by
    rw [isOpen_iff_forall_mem_open]
    intro u huC
    obtain ⟨W, hWaff, huW, _hWU⟩ :=
      exists_isAffineOpen_mem_and_subset (X := U) (x := u) (U := ⊤) trivial
    let uW : W := ⟨u, huW⟩
    have hcompfin : (irreducibleComponents W).Finite :=
      hfinite (W : Set U) W.isOpen hWaff.isCompact
    let S : Set (Set W) :=
      {T | T ∈ irreducibleComponents W ∧ uW ∉ T}
    have hSfin : S.Finite := hcompfin.subset (by
      intro T hT
      exact hT.1)
    have hWopen : IsOpen ((⋃₀ S)ᶜ) := by
      rw [Set.sUnion_eq_biUnion, isOpen_compl_iff]
      exact hSfin.isClosed_biUnion (fun T hT ↦
        isClosed_of_mem_irreducibleComponents T hT.1)
    let O : Set U := ((↑) : W → U) '' ((⋃₀ S)ᶜ)
    have hOopen : IsOpen O := by
      exact W.isOpen.isOpenMap_subtype_val _ hWopen
    have huO : u ∈ O := by
      refine ⟨uW, ?_, rfl⟩
      intro huS
      obtain ⟨T, hTS, huT⟩ := Set.mem_sUnion.mp huS
      exact hTS.2 huT
    have hOsub : O ⊆ C := by
      intro y hy
      obtain ⟨yW, hyW, rfl⟩ := hy
      have hycover : yW ∈ ⋃₀ irreducibleComponents W := by
        rw [sUnion_irreducibleComponents]
        trivial
      obtain ⟨T, hTcomp, hyT⟩ := Set.mem_sUnion.mp hycover
      have huT : uW ∈ T := by
        by_contra huT
        apply hyW
        exact Set.mem_sUnion.mpr ⟨T, ⟨hTcomp, huT⟩, hyT⟩
      let T' : Set U := ((↑) : W → U) '' T
      have hT'irr : IsIrreducible T' := by
        exact hTcomp.1.image _ continuous_subtype_val.continuousOn
      obtain ⟨Z, hZcomp, hTZ⟩ :=
        exists_mem_irreducibleComponents_subset_of_isIrreducible T' hT'irr
      have hyZ : (yW : U) ∈ Z := hTZ ⟨yW, hyT, rfl⟩
      have huZ : u ∈ Z := hTZ ⟨uW, huT, rfl⟩
      rw [hunique u hZcomp hC huZ huC] at hyZ
      exact hyZ
    exact ⟨O, hOsub, hOopen, huO⟩
  exact ⟨hclosed, hopen⟩

end AlgebraicGeometry
