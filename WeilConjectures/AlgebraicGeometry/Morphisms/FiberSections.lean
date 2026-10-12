/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree

/-!
# Global sections of the fibres of an affine morphism

Let `f : X ⟶ Y` be an affine morphism, `V ⊆ Y` an affine open and `y ∈ V`. Then the ring of
global sections of the scheme-theoretic fibre `X_y = f.fiber y` is the base change
`κ(y) ⊗_{Γ(Y, V)} Γ(X, f⁻¹ V)`. Since `κ(y) ⊗_{Γ(Y, V)} M = κ(y) ⊗_{𝒪_{Y,y}} M_y` for any
`Γ(Y, V)`-module `M`, and `Γ(X, f⁻¹ V)_y = (f_* 𝒪_X)_y`, this says that the canonical map
`(f_* 𝒪_X)_y ⊗_{𝒪_{Y,y}} κ(y) → Γ(X_y, 𝒪_{X_y})` is an isomorphism.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.isPushout_app_evaluation_fiber`: the square of rings
  `Γ(Y, V) → Γ(X, f⁻¹ V), κ(y) → Γ(X_y, ⊤)` is a pushout.
- `AlgebraicGeometry.Scheme.Hom.exists_ringEquiv_tensorProduct_fiber`: the canonical map
  `κ(y) ⊗_{Γ(Y, V)} Γ(X, f⁻¹ V) → Γ(X_y, ⊤)` is a ring isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- The canonical morphism `Spec κ(y) ⟶ Y` maps into every open containing `y`. -/
lemma Scheme.preimage_fromSpecResidueField {y : Y} {V : Y.Opens} (hy : y ∈ V) :
    Y.fromSpecResidueField y ⁻¹ᵁ V = ⊤ := by
  ext x
  simpa using hy

/-- On sections over an open `V ∋ y`, the morphism `Spec κ(y) ⟶ Y` is evaluation at `y`. -/
lemma Scheme.fromSpecResidueField_appLE_ΓSpecIso_hom (y : Y) (V : Y.Opens) (hy : y ∈ V) :
    (Y.fromSpecResidueField y).appLE V ⊤ (Y.preimage_fromSpecResidueField hy).ge ≫
      (Scheme.ΓSpecIso _).hom = Y.evaluation V y hy := by
  dsimp only [Scheme.fromSpecResidueField]
  rw [Scheme.Hom.comp_appLE, Scheme.fromSpecStalk_app hy,
    Category.assoc, Category.assoc, Category.assoc, Scheme.Hom.map_appLE_assoc,
    Scheme.Hom.appLE_top_top,
    Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc, Scheme.evaluation]

/-- The fibre of `f` at `y` lies over every open `V ∋ y`. -/
lemma Scheme.Hom.preimage_fiberι_preimage (f : X ⟶ Y) (y : Y) (V : Y.Opens) (hy : y ∈ V) :
    f.fiberι y ⁻¹ᵁ f ⁻¹ᵁ V = ⊤ := by
  rw [← Scheme.Hom.comp_preimage, f.fiber_fac, Scheme.Hom.comp_preimage,
    Y.preimage_fromSpecResidueField hy, Scheme.Hom.preimage_top]

/-- For an affine morphism `f : X ⟶ Y`, an affine open `V ⊆ Y` and `y ∈ V`, the square of rings
with sides `f.app V : Γ(Y, V) ⟶ Γ(X, f⁻¹ V)`, the evaluation `Γ(Y, V) ⟶ κ(y)`, the restriction
`Γ(X, f⁻¹ V) ⟶ Γ(X_y, ⊤)` and the structure map `κ(y) ⟶ Γ(X_y, ⊤)` is a pushout: the global
sections of the fibre `X_y` are `κ(y) ⊗_{Γ(Y, V)} Γ(X, f⁻¹ V)`.

(blueprint: `lem-pc-flf-properties`) -/
theorem Scheme.Hom.isPushout_app_evaluation_fiber (f : X ⟶ Y) [IsAffineHom f] {V : Y.Opens}
    (hV : IsAffineOpen V) (y : Y) (hy : y ∈ V) :
    IsPushout (f.app V) (Y.evaluation V y hy)
      ((f.fiberι y).appLE (f ⁻¹ᵁ V) ⊤ (f.preimage_fiberι_preimage y V hy).ge)
      ((Scheme.ΓSpecIso _).inv ≫ (f.fiberToSpecResidueField y).appTop) := by
  have H := isIso_pushoutSection_of_isAffineOpen (IsPullback.of_hasPullback f
    (Y.fromSpecResidueField y)) (US := V) (UT := ⊤) (UX := f ⁻¹ᵁ V) (UY := ⊤)
    (Y.preimage_fromSpecResidueField hy).ge le_rfl
    (by simp [Scheme.Hom.fiberι.eq_def, ← f.preimage_fiberι_preimage y V hy]) hV
    (isAffineOpen_top _) (hV.preimage f)
  rw [isIso_pushoutSection_iff] at H
  refine H.of_iso (Iso.refl _) (Iso.refl _) (Scheme.ΓSpecIso _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp [Scheme.Hom.app_eq_appLE]
  · simpa using Y.fromSpecResidueField_appLE_ΓSpecIso_hom y V hy
  · simp [Scheme.Hom.fiberι]
  · simp [Scheme.Hom.fiberToSpecResidueField, Scheme.Hom.appLE_top_top]

open TensorProduct in
/-- **Global sections of the fibres of an affine morphism.** For an affine morphism `f : X ⟶ Y`
(e.g. `f` finite locally free), an affine open `V ⊆ Y` and `y ∈ V`, the canonical map
`κ(y) ⊗_{Γ(Y, V)} Γ(X, f⁻¹ V) → Γ(X_y, 𝒪_{X_y})`, `a ⊗ b ↦ a · b|_{X_y}`, is a ring
isomorphism. As `κ(y) ⊗_{Γ(Y, V)} Γ(X, f⁻¹ V) = κ(y) ⊗_{𝒪_{Y,y}} (f_* 𝒪_X)_y`, this is the
statement that `(f_* 𝒪_X)_y ⊗_{𝒪_{Y,y}} κ(y) → Γ(X_y, 𝒪_{X_y})` is an isomorphism.

(blueprint: `lem-pc-flf-properties`) -/
theorem Scheme.Hom.exists_ringEquiv_tensorProduct_fiber (f : X ⟶ Y) [IsAffineHom f]
    {V : Y.Opens} (hV : IsAffineOpen V) (y : Y) (hy : y ∈ V) :
    letI := (f.app V).hom.toAlgebra
    letI := (Y.evaluation V y hy).hom.toAlgebra
    ∃ e : Y.residueField y ⊗[Γ(Y, V)] Γ(X, f ⁻¹ᵁ V) ≃+* Γ(f.fiber y, ⊤),
      ∀ a b, e (a ⊗ₜ b) = ((Scheme.ΓSpecIso _).inv ≫ (f.fiberToSpecResidueField y).appTop) a *
        (f.fiberι y).appLE (f ⁻¹ᵁ V) ⊤ (f.preimage_fiberι_preimage y V hy).ge b := by
  let := (f.app V).hom.toAlgebra
  let := (Y.evaluation V y hy).hom.toAlgebra
  have P := (f.isPushout_app_evaluation_fiber hV y hy).flip
  have T := CommRingCat.isPushout_tensorProduct Γ(Y, V) (Y.residueField y) Γ(X, f ⁻¹ᵁ V)
  let e := T.isoPushout ≪≫ P.isoPushout.symm
  have hl : CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫ e.hom =
      (Scheme.ΓSpecIso _).inv ≫ (f.fiberToSpecResidueField y).appTop := by
    simp only [e, Iso.trans_hom, Iso.symm_hom, ← Category.assoc, IsPushout.inl_isoPushout_hom]
    rw [Iso.comp_inv_eq, IsPushout.inl_isoPushout_hom]
    rfl
  have hr : CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom ≫ e.hom =
      (f.fiberι y).appLE (f ⁻¹ᵁ V) ⊤ (f.preimage_fiberι_preimage y V hy).ge := by
    simp only [e, Iso.trans_hom, Iso.symm_hom, ← Category.assoc, IsPushout.inr_isoPushout_hom]
    rw [Iso.comp_inv_eq, IsPushout.inr_isoPushout_hom]
    rfl
  refine ⟨e.commRingCatIsoToRingEquiv, fun a b ↦ ?_⟩
  rw [← mul_one a, ← one_mul b, ← Algebra.TensorProduct.tmul_mul_tmul, map_mul, mul_one, one_mul]
  exact congr($(hl).hom a * $(hr).hom b)

end AlgebraicGeometry
