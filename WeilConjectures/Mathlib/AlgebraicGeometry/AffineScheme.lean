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

We also record that a quasi-compact open contained in an affine open is a finite union of
basic opens (`AlgebraicGeometry.IsAffineOpen.exists_finset_basicOpen_eq`).
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
  have : IsAffine V.toScheme := hV
  have hW' : IsCompact ((V.ι ⁻¹ᵁ W : V.toScheme.Opens) : Set V.toScheme) :=
    V.ι.isOpenEmbedding.isInducing.isCompact_preimage' hW
      (by rw [Scheme.Opens.range_ι]; exact hWV)
  obtain ⟨Us, hUsB, hUsfin, hUs⟩ :=
    (isBasis_basicOpen V.toScheme).exists_finite_of_isCompact hW'
  have := hUsfin.fintype
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

end AlgebraicGeometry
