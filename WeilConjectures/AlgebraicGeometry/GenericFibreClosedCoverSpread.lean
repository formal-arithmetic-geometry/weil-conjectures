/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.AlgebraicGeometry.GenericFlatness

/-! # Shrinking near a generic fibre

## References

* [Stacks, Tag 054Y], [Stacks, Tag 054W]
-/

@[expose] public section

universe u

open CategoryTheory Topology

namespace AlgebraicGeometry

/-- Two closed subsets covering a fibre cover the family over a neighbourhood in
its base point's closure (Stacks, Tags 054Y, 055N). -/
theorem exists_open_generic_fibre_closed_cover {P T : Scheme.{u}} (g : P ⟶ T)
    [LocallyOfFiniteType g] [QuasiCompact g] (y : T) (C D : Set P)
    (hC : IsClosed C) (hD : IsClosed D) (hcover : g ⁻¹' {y} ⊆ C ∪ D) :
    ∃ V : Set T, IsOpen V ∧ y ∈ V ∧ g ⁻¹' (V ∩ closure {y}) ⊆ C ∪ D := by
  let J := Scheme.IdealSheafData.vanishingIdeal
    (⟨closure {y}, isClosed_closure⟩ : TopologicalSpace.Closeds T)
  let Z := J.subscheme
  let j : Z ⟶ T := J.subschemeι
  have hr : Set.range j = closure {y} := by
    exact J.range_subschemeι.trans
      (Scheme.IdealSheafData.coe_support_vanishingIdeal _)
  have hZirr : IrreducibleSpace Z := by
    have hirr : IsIrreducible (Set.range j) := hr ▸ isIrreducible_singleton.closure
    have := Subtype.irreducibleSpace hirr
    have hu := (IrreducibleSpace.isIrreducible_univ (Set.range j)).image
      j.isEmbedding.toHomeomorph.symm
      j.isEmbedding.toHomeomorph.symm.continuous.continuousOn
    rw [Set.image_univ, j.isEmbedding.toHomeomorph.symm.surjective.range_eq] at hu
    exact (irreducibleSpace_def _).mpr hu
  have hZ : IsIntegral Z := isIntegral_of_irreducibleSpace_of_isReduced Z
  let η : Z := ⟨y, by
    change y ∈ closure {y}
    exact subset_closure (Set.mem_singleton y)⟩
  have hjη : j η = y := rfl
  have hη (z : Z) : η ⤳ z := by
    apply j.isEmbedding.specializes_iff.mp
    rw [hjη, specializes_iff_mem_closure]
    exact hr ▸ Set.mem_range_self z
  let f : Limits.pullback g j ⟶ Z := Limits.pullback.snd g j
  let p : Limits.pullback g j ⟶ P := Limits.pullback.fst g j
  obtain ⟨U, hU, hflat⟩ := exists_nonempty_open_flat_restrict f
  have hηU : η ∈ U := by
    obtain ⟨z, hz⟩ := hU
    exact (hη z).mem_open U.isOpen hz
  obtain ⟨V, hV, hVU⟩ := j.isEmbedding.isInducing.isOpen_iff.mp U.isOpen
  refine ⟨V, hV, ?_, ?_⟩
  · have := hηU
    change η ∈ (U : Set Z) at this
    rw [← hVU] at this
    exact this
  · intro x hx
    obtain ⟨w, hw⟩ : x ∈ Set.range p := by
      rw [Scheme.Pullback.range_fst, hr]
      exact hx.2
    have hfw : f w ∈ U := by
      change f w ∈ (U : Set Z)
      rw [← hVU]
      change j (f w) ∈ V
      have he : j (f w) = g (p w) := by
        exact congrArg (fun k : Limits.pullback g j ⟶ T => k w)
          Limits.pullback.condition.symm
      rw [he, hw]
      exact hx.1
    let wU : (f ⁻¹ᵁ U).toScheme := ⟨w, hfw⟩
    let ηU : U.toScheme := ⟨η, hηU⟩
    have hs : ηU ⤳ (f ∣_ U) wU := by
      apply (subtype_specializes_iff _ _).mpr
      simpa only [morphismRestrict_base_coe] using hη (f w)
    obtain ⟨a, ha, hea⟩ := Flat.generalizingMap (f ∣_ U) hs
    have hfa : f a.1 = η := by
      simpa only [morphismRestrict_base_coe] using congrArg Subtype.val hea
    have hpa : p a.1 ∈ g ⁻¹' {y} := by
      change g (p a.1) = y
      have he : g (p a.1) = j (f a.1) := by
        exact congrArg (fun k : Limits.pullback g j ⟶ T => k a.1)
          Limits.pullback.condition
      rw [he, hfa, hjη]
    have hspec : p a.1 ⤳ x := by
      rw [← hw]
      exact (ha.map (f ⁻¹ᵁ U).ι.continuous).map p.continuous
    exact hspec.mem_closed (hC.union hD) (hcover hpa)

end AlgebraicGeometry
