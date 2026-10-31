/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateSectionProjection

/-! # The old coordinate support in the successor affine tower

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
cor-pur-affine-space-zero-section-purity.proof.md, ordered coordinate product.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option maxRecDepth 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.ProEtale.AffineZeroPurity
open AffineSpacePurity

private theorem tower_hom_ext {B T : Scheme.{u}} (c : ℕ)
    (f g : T ⟶ iteratedAffineLine B c)
    (hp : f ≫ iteratedAffineLineProj B c = g ≫ iteratedAffineLineProj B c)
    (ht : ∀ i, f.appTop (iteratedAffineLine.coord B c i) =
      g.appTop (iteratedAffineLine.coord B c i)) : f = g := by
  induction c with
  | zero =>
    exact (Category.comp_id f).symm.trans (hp.trans (Category.comp_id g))
  | succ c ih =>
    apply AffineSpace.hom_ext (n := PUnit.{u + 1})
    · apply ih
      · have h := hp
        rw [iteratedAffineLineProj_succ] at h
        exact (Category.assoc f _ _).trans (h.trans (Category.assoc g _ _).symm)
      · intro i
        have h := ht i.succ
        rw [iteratedAffineLine.coord_succ_succ] at h
        let p : iteratedAffineLine B (c + 1) ⟶ iteratedAffineLine B c :=
          𝔸(PUnit.{u + 1}; iteratedAffineLine B c) ↘ iteratedAffineLine B c
        exact (show (f ≫ p).appTop _ = f.appTop (p.appTop _) by
          rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]).trans
          (h.trans (show (g ≫ p).appTop _ = g.appTop (p.appTop _) by
            rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]).symm)
    · intro i
      cases i
      exact ht 0

end AlgebraicGeometry.ProEtale.AffineZeroPurity
