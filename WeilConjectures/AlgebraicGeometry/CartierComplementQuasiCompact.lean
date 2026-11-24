/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Quasi-compactness of the open complement of a Cartier divisor

The local principal equations give the scope needed for the supported-Hom
comparison.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory TopologicalSpace
namespace AlgebraicGeometry

/-- The complement of an effective Cartier divisor is quasi-compact. -/
theorem cartierComplement_quasiCompact {D X : Scheme.{u}} (i : D ⟶ X)
    [IsClosedImmersion i] (hI : i.ker.IsInvertible) : QuasiCompact i.openComplement.ι := by
  classical
  choose U hx f hf hgen using hI
  have hU : (⨆ x : X, (U x).1) = ⊤ := by
    apply top_unique
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hx x⟩
  apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := @QuasiCompact) (fun x ↦ (U x).1) hU
  intro x
  let j := i.openComplement.ι
  have himage : j '' (j ⁻¹ᵁ (U x).1 : Set i.openComplement.toScheme) =
      (X.basicOpen (f x) : Set X) := by
    change j '' (j ⁻¹' ((U x).1 : Set X)) = _
    rw [Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι]
    have hs := i.ker.coe_support_inter (U x)
    rw [Scheme.Hom.support_ker, i.isClosedEmbedding.isClosed_range.closure_eq,
      hgen x, Scheme.zeroLocus_span, Scheme.zeroLocus_singleton] at hs
    ext y
    have hmem := Set.ext_iff.mp hs y
    have hle : y ∈ X.basicOpen (f x) → y ∈ (U x).1 :=
      fun h ↦ X.basicOpen_le (f x) h
    simp only [Set.mem_inter_iff, Set.mem_compl_iff] at hmem ⊢
    tauto
  have hc : IsCompact (j ⁻¹ᵁ (U x).1 : Set i.openComplement.toScheme) := by
    apply j.isOpenEmbedding.isEmbedding.isCompact_iff.mpr
    rw [himage]
    exact ((U x).2.basicOpen (f x)).isCompact
  have : IsAffine (U x).1.toScheme := (U x).2
  exact HasAffineProperty.iff_of_isAffine.mpr (isCompact_iff_compactSpace.mp hc)
end AlgebraicGeometry
