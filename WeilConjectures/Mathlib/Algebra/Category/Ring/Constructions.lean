/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.RingTheory.TensorProduct.Pi
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Pushout squares in `CommRingCat`

For an ideal `K` of `R` and a ring map `φ : R ⟶ S`, the square formed by the quotient
maps `R ⟶ R ⧸ K`, `S ⟶ S ⧸ K·S` and the induced map `R ⧸ K ⟶ S ⧸ K·S` is a pushout in
`CommRingCat`.

This is not proved by exhibiting the colimit cocone by hand: it is the tensor-product
pushout `CommRingCat.isPushout_tensorProduct` transported along the isomorphism
`Algebra.TensorProduct.quotIdealMapEquivTensorQuot : S ⧸ K·S ≃ₐ[S] S ⊗[R] (R ⧸ K)`.

A product of two pushout squares is a pushout square, since tensoring commutes with finite
products of rings.

## Main results

- `CommRingCat.isPushout_quotient`
- `CommRingCat.isoIsPushout_tensorProduct_hom_tmul`
- `CommRingCat.isPushout_prod`
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
  let := φ.hom.toAlgebra
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

/-- The isomorphism identifying the corner of a pushout square in `CommRingCat` with a tensor
product sends `r ⊗ₜ b` to the product of the images of `r` and `b`. -/
lemma isoIsPushout_tensorProduct_hom_tmul {R R' B B' : CommRingCat.{u}} [Algebra ↥R ↥R']
    [Algebra ↥R ↥B] {β : B ⟶ B'} {r'B : R' ⟶ B'}
    (h : IsPushout (ofHom (algebraMap ↥R ↥R')) (ofHom (algebraMap ↥R ↥B)) r'B β)
    (r : ↥R') (b : ↥B) :
    ((isPushout_tensorProduct ↥R ↥R' ↥B).isoIsPushout _ _ h).hom (r ⊗ₜ[↥R] b) = r'B r * β b := by
  have hl : ((isPushout_tensorProduct ↥R ↥R' ↥B).isoIsPushout _ _ h).hom
      (r ⊗ₜ[↥R] (1 : ↥B)) = r'B r := by
    have := ConcreteCategory.congr_hom
      ((isPushout_tensorProduct ↥R ↥R' ↥B).inl_isoIsPushout_hom _ _ h) r
    simp only [comp_apply, hom_ofHom, Algebra.TensorProduct.includeLeftRingHom_apply] at this
    exact this
  have hr : ((isPushout_tensorProduct ↥R ↥R' ↥B).isoIsPushout _ _ h).hom
      ((1 : ↥R') ⊗ₜ[↥R] b) = β b := by
    have := ConcreteCategory.congr_hom
      ((isPushout_tensorProduct ↥R ↥R' ↥B).inr_isoIsPushout_hom _ _ h) b
    simp only [comp_apply, hom_ofHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.includeRight_apply] at this
    exact this
  have hx : (r ⊗ₜ[↥R] b : ↥R' ⊗[↥R] ↥B) = (r ⊗ₜ[↥R] (1 : ↥B)) * ((1 : ↥R') ⊗ₜ[↥R] b) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [hx, map_mul, hl, hr]

/-- A product of two pushout squares in `CommRingCat` is a pushout square: base change
commutes with finite products of rings. -/
lemma isPushout_prod {R R' B₁ B₂ B₁' B₂' : CommRingCat.{u}} {φ : R ⟶ R'}
    {r₁ : R ⟶ B₁} {r₂ : R ⟶ B₂} {β₁ : B₁ ⟶ B₁'} {β₂ : B₂ ⟶ B₂'}
    {r'₁ : R' ⟶ B₁'} {r'₂ : R' ⟶ B₂'}
    (h₁ : IsPushout r₁ φ β₁ r'₁) (h₂ : IsPushout r₂ φ β₂ r'₂) :
    IsPushout (ofHom (r₁.hom.prod r₂.hom)) φ
      (ofHom ((β₁.hom.comp (RingHom.fst ↥B₁ ↥B₂)).prod (β₂.hom.comp (RingHom.snd ↥B₁ ↥B₂))))
      (ofHom (r'₁.hom.prod r'₂.hom)) := by
  let : Algebra ↥R ↥R' := φ.hom.toAlgebra
  let : Algebra ↥R ↥B₁ := r₁.hom.toAlgebra
  let : Algebra ↥R ↥B₂ := r₂.hom.toAlgebra
  have hB₁ : IsPushout (ofHom (algebraMap ↥R ↥R')) (ofHom (algebraMap ↥R ↥B₁)) r'₁ β₁ := h₁.flip
  have hB₂ : IsPushout (ofHom (algebraMap ↥R ↥R')) (ofHom (algebraMap ↥R ↥B₂)) r'₂ β₂ := h₂.flip
  let e₁ := (isPushout_tensorProduct ↥R ↥R' ↥B₁).isoIsPushout _ _ hB₁
  let e₂ := (isPushout_tensorProduct ↥R ↥R' ↥B₂).isoIsPushout _ _ hB₂
  have key₁ (r : ↥R') (b : ↥B₁) : e₁.hom (r ⊗ₜ[↥R] b) = r'₁ r * β₁ b :=
    isoIsPushout_tensorProduct_hom_tmul hB₁ r b
  have key₂ (r : ↥R') (b : ↥B₂) : e₂.hom (r ⊗ₜ[↥R] b) = r'₂ r * β₂ b :=
    isoIsPushout_tensorProduct_hom_tmul hB₂ r b
  have ptP := isPushout_tensorProduct ↥R ↥R' (↥B₁ × ↥B₂)
  have hw : φ ≫ ofHom (r'₁.hom.prod r'₂.hom) = ofHom (r₁.hom.prod r₂.hom) ≫
      ofHom ((β₁.hom.comp (RingHom.fst ↥B₁ ↥B₂)).prod (β₂.hom.comp (RingHom.snd ↥B₁ ↥B₂))) := by
    ext r
    · simpa using (ConcreteCategory.congr_hom h₁.w r).symm
    · simpa using (ConcreteCategory.congr_hom h₂.w r).symm
  let Ψ := ptP.desc (ofHom (r'₁.hom.prod r'₂.hom))
    (ofHom ((β₁.hom.comp (RingHom.fst ↥B₁ ↥B₂)).prod (β₂.hom.comp (RingHom.snd ↥B₁ ↥B₂)))) hw
  have hΨ (r : ↥R') (x : ↥B₁ × ↥B₂) :
      Ψ (r ⊗ₜ[↥R] x) = (r'₁ r * β₁ x.1, r'₂ r * β₂ x.2) := by
    have hl : Ψ (r ⊗ₜ[↥R] (1 : ↥B₁ × ↥B₂)) = (r'₁ r, r'₂ r) := by
      have h := ConcreteCategory.congr_hom (ptP.inl_desc _ _ hw) r
      simp only [hom_ofHom] at h
      exact h
    have hr : Ψ ((1 : ↥R') ⊗ₜ[↥R] x) = (β₁ x.1, β₂ x.2) := by
      have h := ConcreteCategory.congr_hom (ptP.inr_desc _ _ hw) x
      simp only [hom_ofHom, AlgHom.toRingHom_eq_coe] at h
      exact h
    have hx : (r ⊗ₜ[↥R] x : ↥R' ⊗[↥R] (↥B₁ × ↥B₂)) =
        (r ⊗ₜ[↥R] (1 : ↥B₁ × ↥B₂)) * ((1 : ↥R') ⊗ₜ[↥R] x) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [hx, map_mul, hl, hr]
    rfl
  have hcomp (z : ↥R' ⊗[↥R] (↥B₁ × ↥B₂)) :
      Ψ z = Prod.map ⇑e₁.hom ⇑e₂.hom
        (Algebra.TensorProduct.prodRight ↥R ↥R' ↥R' ↥B₁ ↥B₂ z) := by
    induction z with
    | zero => simp [Prod.ext_iff]
    | tmul r x =>
      rw [hΨ]
      simp [Algebra.TensorProduct.prodRight_tmul, key₁, key₂]
    | add x y hx hy => simp [map_add, hx, hy, Prod.ext_iff]
  have hbij : Function.Bijective Ψ := by
    have hpm : Function.Bijective (Prod.map ⇑e₁.hom ⇑e₂.hom) :=
      Function.Bijective.prodMap (ConcreteCategory.bijective_of_isIso e₁.hom)
        (ConcreteCategory.bijective_of_isIso e₂.hom)
    have h := hpm.comp (Algebra.TensorProduct.prodRight ↥R ↥R' ↥R' ↥B₁ ↥B₂).bijective
    have heq : ⇑Ψ = (Prod.map ⇑e₁.hom ⇑e₂.hom) ∘
        ⇑(Algebra.TensorProduct.prodRight ↥R ↥R' ↥R' ↥B₁ ↥B₂) := funext hcomp
    rw [heq]
    exact h
  have : IsIso Ψ := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact hbij
  refine ptP.flip.of_iso' (Iso.refl _) (Iso.refl _) (Iso.refl _) (asIso Ψ).symm ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl
  · simp only [Iso.refl_hom, Category.id_comp, Iso.symm_hom, asIso_inv]
    rw [IsIso.eq_comp_inv]
    exact ptP.inr_desc _ _ hw
  · simp only [Iso.refl_hom, Category.id_comp, Iso.symm_hom, asIso_inv]
    rw [IsIso.eq_comp_inv]
    exact ptP.inl_desc _ _ hw

end CommRingCat
