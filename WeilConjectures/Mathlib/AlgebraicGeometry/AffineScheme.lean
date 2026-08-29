/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# `Spec` of a restriction map and the canonical isomorphisms of affine opens

We record that `Spec` of a restriction map between affine opens intertwines the canonical
isomorphisms `Spec Γ(X, U) ≅ U` with the inclusion of opens, and that the algebra map
realizing `Γ(X, X.basicOpen f)` as a localization is the restriction map of the structure
sheaf.

We also record that, for a morphism `f : X ⟶ Y`, the affine opens of `X` contained in the
preimage of an affine open of `Y` form a basis of the topology of `X`
(`AlgebraicGeometry.isBasis_affineOpens_le_preimage`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- The `Spec` of a restriction map intertwines the canonical isomorphisms
`Spec Γ(X, U) ≅ U` with the inclusion of opens. -/
lemma specMap_res_isoSpec_inv {U V : X.affineOpens} (hUV : U ≤ V) :
    Spec.map (X.presheaf.map (homOfLE (X := X.Opens) hUV).op) ≫ V.2.isoSpec.inv =
      U.2.isoSpec.inv ≫ X.homOfLE hUV := by
  rw [← cancel_mono V.1.ι, Category.assoc, Category.assoc, IsAffineOpen.isoSpec_inv_ι,
    Scheme.homOfLE_ι, IsAffineOpen.isoSpec_inv_ι,
    V.2.map_fromSpec U.2 (homOfLE (X := X.Opens) hUV).op]

/-- The algebra map exhibiting the sections over a basic open as a localization is the
restriction map of the structure sheaf. -/
lemma algebraMap_basicOpen_eq {U : X.Opens} (f : Γ(X, U)) :
    algebraMap Γ(X, U) Γ(X, X.basicOpen f) =
      (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom :=
  rfl

/-- A quasi-compact open contained in an affine open `V` of a scheme is a finite union of
basic opens of sections over `V`. -/
theorem IsAffineOpen.exists_finset_basicOpen_eq {X : Scheme.{u}} {V : X.Opens}
    (hV : IsAffineOpen V) {W : X.Opens} (hW : IsCompact (W : Set X)) (hWV : W ≤ V) :
    ∃ s : Finset Γ(X, V), W = ⨆ f ∈ s, X.basicOpen f := by
  classical
  haveI : IsAffine V.toScheme := hV
  have hW' : IsCompact ((V.ι ⁻¹ᵁ W : V.toScheme.Opens) : Set V.toScheme) :=
    V.ι.isOpenEmbedding.isInducing.isCompact_preimage' hW
      (by rw [Scheme.Opens.range_ι]; exact hWV)
  obtain ⟨Us, hUsB, hUsfin, hUs⟩ :=
    (isBasis_basicOpen V.toScheme).exists_finite_of_isCompact hW'
  haveI := hUsfin.fintype
  choose g hg using fun u : Us ↦ hUsB u.2
  refine ⟨Finset.univ.image fun u : Us ↦ V.topIso.hom (g u), ?_⟩
  calc W = V.ι ''ᵁ (V.ι ⁻¹ᵁ W) := by
        rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
          inf_eq_right.mpr hWV]
    _ = ⨆ u : Us, V.ι ''ᵁ (u : V.toScheme.Opens) := by
        rw [hUs, sSup_eq_iSup', Scheme.Hom.image_iSup]
    _ = ⨆ f ∈ Finset.univ.image fun u : Us ↦ V.topIso.hom (g u), X.basicOpen f := by
        rw [Finset.iSup_finset_image]
        simp only [Finset.mem_univ, iSup_pos]
        refine iSup_congr fun u ↦ ?_
        rw [← hg u]
        conv_lhs => rw [← Iso.hom_inv_id_apply V.topIso (g u)]
        exact Scheme.Opens.ι_image_basicOpen_topIso_inv _ _

/-- The affine opens of `X` that are contained in the preimage of an affine open of `Y` form a
basis of the topology of `X`. -/
lemma isBasis_affineOpens_le_preimage {X Y : Scheme.{u}} (f : X ⟶ Y) :
    TopologicalSpace.Opens.IsBasis {W : X.Opens | IsAffineOpen W ∧
      ∃ V : Y.Opens, IsAffineOpen V ∧ W ≤ f ⁻¹ᵁ V} := by
  refine TopologicalSpace.Opens.isBasis_iff_nbhd.mpr fun {U x} hxU ↦ ?_
  obtain ⟨V, hV, hxV, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
    (U := ⊤) (x := f.base x) trivial
  obtain ⟨W, hW, hxW, hWU⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (U := U ⊓ f ⁻¹ᵁ V) ⟨hxU, hxV⟩
  exact ⟨W, ⟨hW, V, hV, hWU.trans inf_le_right⟩, hxW, hWU.trans inf_le_left⟩

/-- A quasi-compact open of an affine scheme is a finite union of basic opens. -/
lemma exists_finite_basicOpen_cover [IsAffine X] {U : X.Opens}
    (hU : IsCompact (U : Set X)) :
    ∃ (ι : Type u) (_ : Finite ι) (u : ι → Γ(X, ⊤)) (_ : ∀ i, X.basicOpen (u i) ≤ U),
      U = ⨆ i, X.basicOpen (u i) := by
  classical
  obtain ⟨t, ht⟩ := hU.elim_finite_subcover
    (fun a : {a : Γ(X, ⊤) // X.basicOpen a ≤ U} ↦ (X.basicOpen a.1 : Set X))
    (fun a ↦ (X.basicOpen a.1).2) (by
      intro x hx
      obtain ⟨a, ha1, ha2⟩ := (isAffineOpen_top X).exists_basicOpen_le (V := U) ⟨x, hx⟩ trivial
      exact Set.mem_iUnion.mpr ⟨⟨a, ha1⟩, ha2⟩)
  refine ⟨{a : {a : Γ(X, ⊤) // X.basicOpen a ≤ U} // a ∈ t}, inferInstance,
    fun a ↦ a.1.1, fun a ↦ a.1.2, le_antisymm ?_ (iSup_le fun a ↦ a.1.2)⟩
  intro x hx
  obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp (ht hx)
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨a, ha⟩, hxa⟩

end AlgebraicGeometry
