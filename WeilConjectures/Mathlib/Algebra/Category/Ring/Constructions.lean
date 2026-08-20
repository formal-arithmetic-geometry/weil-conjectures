/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Quotients by extended ideals are pushouts

For an ideal `K` of `R` and a ring map `φ : R ⟶ S`, the square formed by the quotient
maps `R ⟶ R ⧸ K`, `S ⟶ S ⧸ K·S` and the induced map `R ⧸ K ⟶ S ⧸ K·S` is a pushout in
`CommRingCat`.

This is not proved by exhibiting the colimit cocone by hand: it is the tensor-product
pushout `CommRingCat.isPushout_tensorProduct` transported along the isomorphism
`Algebra.TensorProduct.quotIdealMapEquivTensorQuot : S ⧸ K·S ≃ₐ[S] S ⊗[R] (R ⧸ K)`.

## Main results

- `CommRingCat.isPushout_quotient`
-/

@[expose] public section

universe u

open CategoryTheory TensorProduct

namespace CommRingCat

/-- Quotients by extended ideals are pushouts in `CommRingCat`: base change of the closed
immersion cut out by `K` along `φ` is the closed immersion cut out by the extended ideal. -/
lemma isPushout_quotient {R S : CommRingCat.{u}} (φ : R ⟶ S) (K : Ideal R) :
    IsPushout (ofHom (Ideal.Quotient.mk K)) φ
      (ofHom (Ideal.quotientMap (K.map φ.hom) φ.hom Ideal.le_comap_map))
      (ofHom (Ideal.Quotient.mk (K.map φ.hom))) := by
  letI := φ.hom.toAlgebra
  let e : of (S ⧸ K.map φ.hom) ≅ of (S ⊗[R] (R ⧸ K)) :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S K).toRingEquiv.toCommRingCatIso
  refine (isPushout_tensorProduct R S (R ⧸ K)).flip.of_iso' (Iso.refl _) (Iso.refl _)
    (Iso.refl _) e ?_ ?_ ?_ ?_
  · ext r
    simp
  · ext r
    rfl
  · ext r
    simp only [e, Iso.refl_hom, Category.id_comp, RingEquiv.toCommRingCatIso_hom, hom_comp,
      hom_ofHom, RingHom.comp_apply, Ideal.quotientMap_mk, AlgEquiv.coe_ringEquiv,
      RingEquiv.coe_toRingHom, AlgHom.toRingHom_eq_coe]
    exact (Algebra.TensorProduct.tmul_one_eq_one_tmul r).symm
  · ext r
    exact (Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk S K r).symm

end CommRingCat
