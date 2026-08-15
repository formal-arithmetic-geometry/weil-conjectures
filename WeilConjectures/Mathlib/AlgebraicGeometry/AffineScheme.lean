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
isomorphisms `Spec Γ(X, U) ≅ U` with the inclusion of opens, and compute the section map
of a morphism of the form `Spec.map φ ≫ fromSpec`.
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

/-- The section map of `Spec.map φ ≫ fromSpec` from the affine open to the total
sections is `φ` composed with the global-sections isomorphism of the spectrum. -/
lemma appLE_specMap_comp_fromSpec (U : X.affineOpens) {S : CommRingCat.{u}}
    (φ : Γ(X, U.1) ⟶ S) (h : (⊤ : (Spec S).Opens) ≤ (Spec.map φ ≫ U.2.fromSpec) ⁻¹ᵁ U.1) :
    (Spec.map φ ≫ U.2.fromSpec).appLE U.1 ⊤ h = φ ≫ (Scheme.ΓSpecIso S).inv := by
  have e₁ : (⊤ : (Spec Γ(X, U.1)).Opens) ≤ U.2.fromSpec ⁻¹ᵁ U.1 :=
    U.2.fromSpec_preimage_self.ge
  have e₂ : (⊤ : (Spec S).Opens) ≤ Spec.map φ ⁻¹ᵁ ⊤ := le_rfl
  rw [← Scheme.Hom.appLE_comp_appLE (Spec.map φ) U.2.fromSpec U.1 ⊤ ⊤ e₁ e₂]
  have h1 : U.2.fromSpec.appLE U.1 ⊤ e₁ = (Scheme.ΓSpecIso Γ(X, U.1)).inv := by
    rw [Scheme.Hom.appLE, U.2.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    rw [show (eqToHom U.2.fromSpec_preimage_self).op ≫ (homOfLE e₁).op = 𝟙 _ from
      Subsingleton.elim _ _]
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
  have h2 : (Spec.map φ).appLE ⊤ ⊤ e₂ =
      (Scheme.ΓSpecIso Γ(X, U.1)).hom ≫ φ ≫ (Scheme.ΓSpecIso S).inv := by
    have hTop : (Spec.map φ).appLE ⊤ ⊤ e₂ = (Spec.map φ).appTop :=
      Scheme.Hom.appLE_eq_app (Spec.map φ)
    rw [hTop, Scheme.ΓSpecIso_inv_naturality, ← Category.assoc, Iso.hom_inv_id,
      Category.id_comp]
  rw [h1, h2, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end AlgebraicGeometry
