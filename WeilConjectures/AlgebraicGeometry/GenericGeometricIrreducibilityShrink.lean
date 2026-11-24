/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

import WeilConjectures.AlgebraicGeometry.GenericOpenGeometricFibreDensity
import WeilConjectures.AlgebraicGeometry.AffineSourceGeometricIrreducibilityShrink

/-! # Spreading geometric irreducibility from the generic fibre

## References

* Stacks, Tag 0559
-/

@[expose] public section

universe u
open CategoryTheory Topology
namespace AlgebraicGeometry

/-- A finite type morphism with geometrically irreducible generic fibre has
geometrically irreducible fibres near the generic point (Stacks, Tag 0559). -/
theorem exists_open_generic_geometric_irreducibility_shrink {X T : Scheme.{u}}
    (f : X ⟶ T) [LocallyOfFiniteType f] [QuasiCompact f]
    (η : T) (hη : IsGenericPoint η Set.univ)
    (hgeom : GeometricallyIrreducible (f.fiberToSpecResidueField η)) :
    ∃ U : T.Opens, η ∈ U ∧ ∀ t, t ∈ U →
      GeometricallyIrreducible (f.fiberToSpecResidueField t) := by
  have := hgeom
  obtain ⟨V, hV, hηV, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := T) (U := ⊤) (show η ∈ (⊤ : T.Opens) from trivial)
  have : IrreducibleSpace (f.fiber η) :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton
      (f.fiberToSpecResidueField η)
  obtain ⟨x⟩ := (inferInstance : Nonempty (f.fiber η))
  have hxη : f (f.fiberι η x) = η := by
    have hx := (f.range_fiberι η).le ⟨x, rfl⟩
    exact hx
  obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset
    (show f.fiberι η x ∈ f ⁻¹ᵁ V by
      change f (f.fiberι η x) ∈ V
      rw [hxη]
      exact hηV)
  have : IsAffine W.toScheme := hW
  have himage : Set.range (W.ι ≫ f) ⊆ V := by
    rintro t ⟨w, rfl⟩
    exact hWV w.property
  have hWne : Nonempty ((W.ι ≫ f).fiber η) := by
    apply ((W.ι ≫ f).fiberHomeo η).nonempty_congr.mpr
    exact ⟨⟨⟨f.fiberι η x, hxW⟩, hxη⟩⟩
  let i := Limits.pullback.map (W.ι ≫ f) (T.fromSpecResidueField η) f
    (T.fromSpecResidueField η) W.ι (𝟙 _) (𝟙 _) (by simp) (by simp)
  have hi : IsOpenImmersion i := by
    infer_instance
  have hif : i ≫ f.fiberToSpecResidueField η =
      (W.ι ≫ f).fiberToSpecResidueField η := by
    simp [i, Scheme.Hom.fiberToSpecResidueField]
  have hsurj : Surjective (i ≫ f.fiberToSpecResidueField η) := by
    refine ⟨fun t ↦ ?_⟩
    exact ⟨Nonempty.some hWne, Subsingleton.elim _ _⟩
  have hWgeom : GeometricallyIrreducible ((W.ι ≫ f).fiberToSpecResidueField η) := by
    rw [← hif]
    infer_instance
  obtain ⟨U₁, hη₁, hdense⟩ :=
    exists_open_geometric_fibre_dense_of_open f W η hη hgeom hWgeom
  obtain ⟨U₂, hη₂, hgeom₂⟩ :=
    exists_open_affine_source_geometric_irreducibility_shrink
      (W.ι ≫ f) V hV himage η hη hWgeom
  refine ⟨U₁ ⊓ U₂, ⟨hη₁, hη₂⟩, ?_⟩
  intro t ht
  rw [GeometricallyIrreducible.eq_geometrically,
    geometrically_iff_of_isClosedUnderIsomorphisms]
  intro K _ z
  have hchart := hgeom₂ t ht.2
  have hirr : IrreducibleSpace
      ↥(Limits.pullback ((W.ι ≫ f).fiberToSpecResidueField t) z) :=
    hchart.geometrically_irreducibleSpace z _ _ (.of_hasPullback _ _)
  let m := Limits.pullback.map ((W.ι ≫ f).fiberToSpecResidueField t) z
    (f.fiberToSpecResidueField t) z
    (Limits.pullback.map (W.ι ≫ f) (T.fromSpecResidueField t) f
      (T.fromSpecResidueField t) W.ι (𝟙 _) (𝟙 _) (by simp) (by simp))
    (𝟙 _) (𝟙 _) (by simp [Scheme.Hom.fiberToSpecResidueField]) (by simp)
  have hm : DenseRange m := hdense t ht.1 K z
  apply (irreducibleSpace_def _).mpr
  change IsIrreducible (Set.univ : Set ↥(Limits.pullback (f.fiberToSpecResidueField t) z))
  rw [← hm.closure_range, ← Set.image_univ]
  exact ((IrreducibleSpace.isIrreducible_univ _).image m
    m.continuous.continuousOn).closure

end AlgebraicGeometry
