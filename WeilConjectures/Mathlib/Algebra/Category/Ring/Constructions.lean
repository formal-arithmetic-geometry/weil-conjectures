/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import WeilConjectures.Mathlib.Algebra.Ring.Subring.Basic

/-!
# Quotients by extended ideals are pushouts

For an ideal `K` of `R` and a ring map `φ : R ⟶ S`, the square formed by the quotient
maps `R ⟶ R ⧸ K`, `S ⟶ S ⧸ K·S` and the induced map `R ⧸ K ⟶ S ⧸ K·S` is a pushout in
`CommRingCat`.

This is not proved by exhibiting the colimit cocone by hand: it is the tensor-product
pushout `CommRingCat.isPushout_tensorProduct` transported along the isomorphism
`Algebra.TensorProduct.quotIdealMapEquivTensorQuot : S ⧸ K·S ≃ₐ[S] S ⊗[R] (R ⧸ K)`.

We also record that the statement "the ranges of two ring maps into `R` generate `R`" is
invariant under an isomorphism of `R` (`CommRingCat.closure_range_union_eq_top_iff_of_iso`).

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

/-- Transporting "the ranges of `a` and `b` generate" along an isomorphism of the target. -/
lemma closure_range_union_eq_top_of_iso {A B R R' : CommRingCat.{u}}
    {a : A ⟶ R} {b : B ⟶ R} (e : R ⟶ R') [IsIso e]
    (h : Subring.closure (Set.range ⇑a.hom ∪ Set.range ⇑b.hom) = ⊤) :
    Subring.closure (Set.range ⇑(a ≫ e).hom ∪ Set.range ⇑(b ≫ e).hom) = ⊤ := by
  have he : Function.Surjective ⇑e.hom := (ConcreteCategory.bijective_of_isIso e).2
  have := _root_.Subring.closure_image_eq_top e.hom he h
  rwa [Set.image_union, ← Set.range_comp, ← Set.range_comp] at this

/-- "The ranges of `a` and `b` generate" is invariant under an isomorphism of the target. -/
lemma closure_range_union_eq_top_iff_of_iso {A B R R' : CommRingCat.{u}}
    {a : A ⟶ R} {b : B ⟶ R} (e : R ⟶ R') [IsIso e] :
    Subring.closure (Set.range ⇑(a ≫ e).hom ∪ Set.range ⇑(b ≫ e).hom) = ⊤ ↔
      Subring.closure (Set.range ⇑a.hom ∪ Set.range ⇑b.hom) = ⊤ := by
  refine ⟨fun h ↦ ?_, closure_range_union_eq_top_of_iso e⟩
  have := closure_range_union_eq_top_of_iso (a := a ≫ e) (b := b ≫ e) (inv e) h
  simpa using this

end CommRingCat
