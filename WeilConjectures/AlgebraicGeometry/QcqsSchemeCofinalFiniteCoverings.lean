/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Topology.Sets.OpenCover

/-! # Cofinal finite affine open coverings of a qcqs scheme

## References

* [Stacks Project, Tag 01IT](https://stacks.math.columbia.edu/tag/01IT)
* [Stacks Project, Tag 01KO](https://stacks.math.columbia.edu/tag/01KO)
* [Stacks Project, Tag 00E8](https://stacks.math.columbia.edu/tag/00E8)
-/

@[expose] public section

universe u v

namespace AlgebraicGeometry

/-- Every open covering of a quasi-compact quasi-separated scheme has a finite affine open
refinement with quasi-compact pairwise intersections. Thus these finite coverings are cofinal
under refinement, as required in Stacks, Modules, Tag 01BS (3), and Sheaves, Tag 009F (4).
-/
theorem qcqs_scheme_cofinal_finite_affine_open_coverings
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    {A : Type v} (V : A → X.Opens) (hV : TopologicalSpace.IsOpenCover V) :
    ∃ (J : Type u) (_ : Finite J) (U : J → X.Opens) (a : J → A),
      TopologicalSpace.IsOpenCover U ∧
      (∀ j, IsAffineOpen (U j)) ∧
      (∀ j, U j ≤ V (a j)) ∧
      (∀ j j', IsCompact ((U j : Set X) ∩ (U j' : Set X))) := by
  classical
  have htop : ⨆ a, V a = ⊤ := hV.iSup_eq_top
  choose a ha using fun x : X ↦ (TopologicalSpace.Opens.mem_iSup.mp
    (show x ∈ (⨆ a, V a) from htop.symm ▸ Set.mem_univ x))
  choose U hUaff hxU hUsub using fun x : X ↦
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (ha x))
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X ↦ (U x : Set X)) (fun x ↦ (U x).isOpen) (by
      intro x hx
      rw [Set.mem_iUnion]
      exact ⟨x, hxU x⟩)
  let J := {x : X // x ∈ t}
  let U' : J → X.Opens := fun j ↦ U j.1
  let a' : J → A := fun j ↦ a j.1
  refine ⟨J, inferInstance, U', a', ?_, ?_, ?_, ?_⟩
  · apply TopologicalSpace.IsOpenCover.mk
    apply le_antisymm le_top
    intro x hx
    rw [TopologicalSpace.Opens.mem_iSup]
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (ht (Set.mem_univ x))
    obtain ⟨hi, hxi⟩ := Set.mem_iUnion.mp hxi
    exact ⟨⟨i, hi⟩, hxi⟩
  · intro j
    exact hUaff j.1
  · intro j
    exact hUsub j.1
  · intro j j'
    exact QuasiSeparatedSpace.inter_isCompact _ _ (U' j).isOpen (hUaff j).isCompact
      (U' j').isOpen (hUaff j').isCompact

end AlgebraicGeometry
