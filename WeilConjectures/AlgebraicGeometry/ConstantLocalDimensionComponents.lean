/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.Properties

/-! # Components of an open of constant local dimension

Source: Stacks Project, Tags 0052 (2), (3), and 0055 (local dimension).
-/

@[expose] public section

universe u
open Topology TopologicalSpace
namespace AlgebraicGeometry

private theorem dimension_le_of_local_dimension_eq
    {A : Type u} [TopologicalSpace A] [QuasiSober A] [T0Space A] (n : ℕ)
    (h : ∀ x : A, topologicalKrullDimAt x = (n : WithBot ℕ∞)) :
    topologicalKrullDim A ≤ (n : WithBot ℕ∞) := by
  let I := {D : TopologicalSpace.Opens A // topologicalKrullDim D ≤ (n : WithBot ℕ∞)}
  let D : I → TopologicalSpace.Opens A := fun i ↦ i.1
  have hcover : (⨆ i, D i) = ⊤ := by
    apply top_unique
    intro x _
    have hxlt : topologicalKrullDimAt x < (n : WithBot ℕ∞) + 1 := by
      rw [h x]
      exact ENat.WithBot.lt_add_one_iff.mpr le_rfl
    obtain ⟨E, hE⟩ := iInf_lt_iff.mp hxlt
    obtain ⟨hxE, hEdim⟩ := iInf_lt_iff.mp hE
    exact (le_iSup D ⟨E, ENat.WithBot.lt_add_one_iff.mp hEdim⟩) hxE
  exact topologicalKrullDim_le_of_iSup_eq_top D hcover _ (fun i ↦ i.2)

/-- Constant finite local dimension on a locally noetherian open gives pure dimension
(Stacks, Tags 0052 and 0055). -/
theorem topologicalKrullDim_component_eq_of_constant_local_dimension
    {Y : Scheme.{u}} [IsLocallyNoetherian Y] (O : Y.Opens) (n : ℕ)
    (hdim : ∀ x ∈ O, topologicalKrullDimAt x = (n : WithBot ℕ∞))
    (C : Set O) (hC : C ∈ irreducibleComponents ↥O) :
    topologicalKrullDim C = (n : WithBot ℕ∞) := by
  have hlocal : ∀ x : O.toScheme, topologicalKrullDimAt x = (n : WithBot ℕ∞) := by
    intro x
    exact (O.isOpen.topologicalKrullDimAt_eq (x := x.1) x.property).trans
      (hdim x.1 x.property)
  have hbound := dimension_le_of_local_dimension_eq n hlocal
  apply le_antisymm
  · exact IsInducing.subtypeVal.topologicalKrullDim_le.trans hbound
  · obtain ⟨c, hc⟩ := hC.1.nonempty
    let A := O.toScheme.affineCover
    let i := A.idx c
    let f := A.f i
    obtain ⟨a, ha⟩ := A.covers c
    have hpre : f ⁻¹' C ∈ irreducibleComponents (A.X i) :=
      preimage_mem_irreducibleComponents hC f.isOpenEmbedding ⟨c, hc, a, ha⟩
    have : IsNoetherianRing Γ(A.X i, ⊤) :=
      IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
    have : NoetherianSpace (A.X i) := noetherianSpace_of_isAffine
    obtain ⟨D, hD, hDne, hDC⟩ :=
      NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _ hpre
    let E : TopologicalSpace.Opens O.toScheme := ⟨f '' D, f.isOpenEmbedding.isOpenMap _ hD⟩
    have hEC : (E : Set O.toScheme) ⊆ C := by
      rintro x ⟨d, hd, rfl⟩
      exact hDC hd
    obtain ⟨d, hd⟩ := hDne
    have hxE : f d ∈ E := ⟨d, hd, rfl⟩
    have hle : (n : WithBot ℕ∞) ≤ topologicalKrullDim E := by
      rw [← hlocal (f d)]
      exact iInf₂_le E hxE
    refine hle.trans ?_
    let j : E → C := fun x ↦ ⟨x.1, hEC x.property⟩
    apply IsInducing.topologicalKrullDim_le (f := j)
    exact IsInducing.of_comp (g := Subtype.val) (by fun_prop)
      continuous_subtype_val IsInducing.subtypeVal

end AlgebraicGeometry
