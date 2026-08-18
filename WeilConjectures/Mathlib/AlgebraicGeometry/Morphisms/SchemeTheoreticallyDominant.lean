/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Scheme-theoretically dominant open subschemes

We record permanence properties of scheme-theoretically dense opens, i.e. opens `U ⊆ X`
whose inclusion `U.ι` is scheme-theoretically dominant:

- `AlgebraicGeometry.IsSchemeTheoreticallyDominant.homOfLE`: if `U ≤ W` and `U` is
  scheme-theoretically dense in `X`, then the inclusion `U ⟶ W` of the intermediate
  open subscheme is scheme-theoretically dominant;
- `AlgebraicGeometry.IsSchemeTheoreticallyDominant.preimage_ι_of_isIso`: the preimage
  of a scheme-theoretically dense open under an isomorphism is scheme-theoretically
  dense;
- `AlgebraicGeometry.IsSchemeTheoreticallyDominant.preimage_ι_of_le`: if `f : X' ⟶ X`
  restricts to an isomorphism over `W`, the open `f ⁻¹ᵁ W` is scheme-theoretically
  dense in `X'` and `U ≤ W` is scheme-theoretically dense in `X`, then `f ⁻¹ᵁ U` is
  scheme-theoretically dense in `X'`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {X' X : Scheme.{u}}

/-- If `U ≤ W` are opens of `X` with `U` scheme-theoretically dense in `X`, then the
inclusion of `U` into the intermediate open subscheme `W` is scheme-theoretically
dominant. -/
theorem IsSchemeTheoreticallyDominant.homOfLE {U W : X.Opens} (h : U ≤ W)
    [QuasiCompact U.ι] [IsSchemeTheoreticallyDominant U.ι] :
    IsSchemeTheoreticallyDominant (X.homOfLE h) := by
  haveI hd : IsSchemeTheoreticallyDominant (X.homOfLE (inf_le_right : U ⊓ W ≤ W)) :=
    .of_isPullback (isPullback_opens_inf U W)
  have he : X.homOfLE h =
      (X.isoOfEq (inf_eq_left.mpr h)).inv ≫ X.homOfLE (inf_le_right : U ⊓ W ≤ W) := by
    rw [← cancel_mono W.ι, Category.assoc, Scheme.homOfLE_ι, Scheme.homOfLE_ι,
      Scheme.isoOfEq_inv_ι]
  rw [he]
  infer_instance

/-- The preimage of a scheme-theoretically dense open subscheme under an isomorphism is
scheme-theoretically dense. -/
theorem IsSchemeTheoreticallyDominant.preimage_ι_of_isIso (f : X' ⟶ X) [IsIso f]
    (O : X.Opens) [IsSchemeTheoreticallyDominant O.ι] :
    IsSchemeTheoreticallyDominant (f ⁻¹ᵁ O).ι := by
  have he : (f ⁻¹ᵁ O).ι = (f ∣_ O) ≫ O.ι ≫ inv f := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  rw [he]
  infer_instance

/-- The restriction of `f` to an open `U ≤ W` is an isomorphism whenever the
restriction of `f` to `W` is. -/
theorem isIso_morphismRestrict_of_le (f : X' ⟶ X) {U W : X.Opens} (h : U ≤ W)
    (hW : IsIso (f ∣_ W)) : IsIso (f ∣_ U) := by
  have himg : W.ι ''ᵁ (W.ι ⁻¹ᵁ U) = U := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr h]
  have hiso : IsIso ((f ∣_ W) ∣_ (W.ι ⁻¹ᵁ U)) := inferInstance
  exact (MorphismProperty.arrow_mk_iso_iff (.isomorphisms Scheme)
    (morphismRestrictRestrict f W (W.ι ⁻¹ᵁ U) ≪≫ morphismRestrictEq f himg)).mp hiso

/-- **Scheme-theoretic density descends along partial isomorphisms**: let
`f : X' ⟶ X` be a morphism restricting to an isomorphism over an open `W ⊆ X` whose
preimage is scheme-theoretically dense in `X'`. Then the preimage of any
scheme-theoretically dense open `U ≤ W` of `X` is scheme-theoretically dense
in `X'`. -/
theorem IsSchemeTheoreticallyDominant.preimage_ι_of_le (f : X' ⟶ X) {U W : X.Opens}
    (hUW : U ≤ W) [QuasiCompact U.ι] [IsSchemeTheoreticallyDominant U.ι]
    (hW : IsIso (f ∣_ W)) [IsSchemeTheoreticallyDominant (f ⁻¹ᵁ W).ι] :
    IsSchemeTheoreticallyDominant (f ⁻¹ᵁ U).ι := by
  haveI hU : IsIso (f ∣_ U) := isIso_morphismRestrict_of_le f hUW hW
  haveI := hW
  have hpre : f ⁻¹ᵁ U ≤ f ⁻¹ᵁ W := f.preimage_mono hUW
  -- the square `(f ∣_ U) ≫ homOfLE hUW = homOfLE hpre ≫ (f ∣_ W)`
  have hsq : X'.homOfLE hpre = (f ∣_ U) ≫ X.homOfLE hUW ≫ inv (f ∣_ W) := by
    rw [eq_comm, ← Category.assoc, IsIso.comp_inv_eq, ← cancel_mono W.ι]
    simp [morphismRestrict_ι, Scheme.homOfLE_ι_assoc, Scheme.homOfLE_ι]
  haveI : IsSchemeTheoreticallyDominant (X.homOfLE hUW) := .homOfLE hUW
  haveI : IsSchemeTheoreticallyDominant (X'.homOfLE hpre) := by
    rw [hsq]; infer_instance
  have he : (f ⁻¹ᵁ U).ι = X'.homOfLE hpre ≫ (f ⁻¹ᵁ W).ι := (Scheme.homOfLE_ι _ _).symm
  rw [he]
  infer_instance

end AlgebraicGeometry
