/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateProductsAgree.CoordinateProductComparison

/-! # Successor support transport

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
cor-pur-affine-space-zero-section-purity.proof.md, ordered exterior product, support
normalization and even shifts
(blueprint: lem-pur-coordinate-product-cons-support-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.ProEtale.AffineZeroPurity
open AffineSpacePurity AffineLinePurity

/-- Successor support transport data.
Source: support normalization in the affine-space zero-section proof
(blueprint: lem-pur-coordinate-product-cons-support-data).

Proof: the successor supports are the pullbacks of `supportMap B c is` and
`supportMap B c js` along the same divisor inclusion `inclusion B c i`. The given
isomorphism `e` with `e.hom ≫ supportMap B c js = supportMap B c is` induces the map
of pullbacks `pullback.map` with components `e.hom`, `𝟙`, `𝟙`, which is an isomorphism
since its three components are. Its composite with the successor support map
`pullback.fst ≫ supportMap B c js` is `pullback.fst ≫ e.hom ≫ supportMap B c js =
pullback.fst ≫ supportMap B c is`. The lengths are both successors of equal lengths. -/
theorem coordinate_product_cons_support_data (P : PurityFiniteSetting.{u}) (n : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of P.field.k)) (c : ℕ) (i : Fin c)
    {is js : List (Fin c)} (h : CoordinateProductsAgree P n B aB c is js) :
    ∃ (e : support B c (i :: is) ≅ support B c (i :: js)),
      e.hom ≫ supportMap B c (i :: js) = supportMap B c (i :: is) ∧
      (i :: is).length = (i :: js).length := by
  obtain ⟨e, he, hlen, -⟩ := h
  have h₁ : supportMap B c is ≫ 𝟙 (iteratedAffineLine B c) = e.hom ≫ supportMap B c js := by
    rw [Category.comp_id, he]
  have h₂ : inclusion B c i ≫ 𝟙 (iteratedAffineLine B c) =
      𝟙 (divisor B c i) ≫ inclusion B c i := by
    rw [Category.comp_id, Category.id_comp]
  refine ⟨asIso (pullback.map (supportMap B c is) (inclusion B c i)
    (supportMap B c js) (inclusion B c i) e.hom (𝟙 (divisor B c i))
    (𝟙 (iteratedAffineLine B c)) h₁ h₂), ?_, by simp [hlen]⟩
  change pullback.map _ _ _ _ _ _ _ h₁ h₂ ≫
      (pullback.fst (supportMap B c js) (inclusion B c i) ≫ supportMap B c js) =
    pullback.fst (supportMap B c is) (inclusion B c i) ≫ supportMap B c is
  rw [pullback.lift_fst_assoc, Category.assoc, he]

end AlgebraicGeometry.ProEtale.AffineZeroPurity
