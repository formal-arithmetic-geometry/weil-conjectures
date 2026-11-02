/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.PurityAffineLineBoundaryRealization
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedHomPullback
public import WeilConjectures.AlgebraicGeometry.SupportedConstantNormalization.SupportedConstantExchangeNormalization
import WeilConjectures.CategoryTheory.ExactBaseChangeSingle
import all WeilConjectures.AlgebraicGeometry.Fixed.FixedComparisonDirectImageMate

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.RetractedSupport
namespace WeilConjectures.PurityFiniteSetting

private theorem normalized_closed_component (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    AlgebraicGeometry.SupportedConstantNormalization.gamma P.Coefficient (zeroSection T) ≫
      (lowerStar (Modules P) (zeroSection T)).map
        (comparisonUpperStarUnitIso P.Coefficient T).inv =
    (lowerStarComparisonUpperStarBaseChange (zeroSection T) (Modules P)).app
      (P.constantEtale T) := by
  let d := upperStarLowerStarAdjunction (Modules P) (zeroSection T)
  have hp : AlgebraicGeometry.SupportedConstantNormalization.comparePullback
      P.Coefficient (zeroSection T) =
      (comparisonUpperStarCompUpperStarIso (Modules P) (zeroSection T)).symm := by
    rfl
  unfold AlgebraicGeometry.SupportedConstantNormalization.gamma
  rw [hp]
  change d.homEquiv _ _ (_ ≫ _ ≫ _) ≫ _ = _
  rw [← d.homEquiv_naturality_right]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [AlgebraicGeometry.ProEtale.underived_comparison_mate]
  rfl

/-- The derived closed-image mate is natural on a represented map.
Source: current blueprint, cor-pur-affine-space-zero-section-purity.proof.md,
finite etale-origin transport paragraph.
(blueprint: lem-pur-coordinate-boundary-image-hom-comparison-mate).
Proof: under the supplied normalized closed exchange, identify the
bounded-below mate with the canonical right-derived base-change map using
its unit equation. Naturality on the represented map,
followed by the exact single-object and unbounded compatibility isomorphisms,
is precisely the displayed factorization by boundaryImageComparison. -/
theorem coordinateBoundaryImageHomComparison_mate
    (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (v : siteSupportHomTransport P (zeroSection T))
    (hclosed : v.closedIso.hom =
      AlgebraicGeometry.SupportedConstantNormalization.gamma P.Coefficient
          (zeroSection T) ≫
        (ProEtale.lowerStar (Modules P) (zeroSection T)).map
          (ProEtale.comparisonUpperStarUnitIso P.Coefficient T).inv)
    (B : DerivedCategory.Plus (EtSheaves P T))
    (b : (DerivedCategory.singleFunctor (EtSheaves P T) 0).obj
      (P.constantEtale T) ⟶ B.obj) :
    ((lowerStar (Modules P) (zeroSection T)).mapDerivedCategorySingleFunctor 0).inv.app
        (P.constant T) ≫
      (lowerStar (Modules P) (zeroSection T)).mapDerivedCategory.map
        (((comparisonUpperStar (Modules P) T).mapDerivedCategorySingleFunctor 0).inv.app
          (P.constantEtale T) ≫ (nu P T).map b) =
    (DerivedCategory.singleFunctor (ProSheaves P (Line T)) 0).map v.closedIso.inv ≫
      ((comparisonUpperStar (Modules P) (Line T)).mapDerivedCategorySingleFunctor 0).inv.app
        ((Etale.lowerStar (Modules P) (zeroSection T)).obj (P.constantEtale T)) ≫
      (nu P (Line T)).map
        (((Etale.lowerStar (Modules P) (zeroSection T)).mapDerivedCategorySingleFunctor
          0).inv.app (P.constantEtale T) ≫
            (Etale.lowerStar (Modules P) (zeroSection T)).mapDerivedCategory.map b) ≫
      P.boundaryImageComparison T B := by
  let S : DerivedCategory.Plus
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) :=
    (DerivedCategory.Plus.singleFunctor (EtSheaves P T) 0).obj (P.constantEtale T)
  let bp : (DerivedCategory.Plus.ι
      (C := Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))).obj S ⟶
      (DerivedCategory.Plus.ι
        (C := Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))).obj B := b
  let bplus := (DerivedCategory.Plus.ι
      (C := Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))).preimage bp
  have hb : DerivedCategory.Plus.ι.map bplus = b :=
    DerivedCategory.Plus.ι.map_preimage bp
  have h := CategoryTheory.Functor.exactBaseChange_represented_unbounded
    (Etale.lowerStar (Modules P) (zeroSection T))
    (lowerStar (Modules P) (zeroSection T))
    (comparisonUpperStar (Modules P) T)
    (comparisonUpperStar (Modules P) (Line T))
    (lowerStarComparisonUpperStarBaseChange (zeroSection T) (Modules P))
    (P.constantEtale T) B bplus
  rw [hb] at h
  have he : v.closedIso.hom =
      (lowerStarComparisonUpperStarBaseChange (zeroSection T) (Modules P)).app
        (P.constantEtale T) := hclosed.trans (normalized_closed_component P T)
  apply (cancel_epi ((DerivedCategory.singleFunctor (ProSheaves P (Line T)) 0).map
    v.closedIso.hom)).1
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id]
  rw [he]
  unfold boundaryImageComparison imageComparison
  dsimp only [Functor.mapDerivedCategoryPlusCompatibility, Iso.app_hom,
    Iso.app_inv, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp,
    CategoryTheory.Functor.map_id, Category.comp_id]
  dsimp only [nu, nuPlus, constant, comparisonDirectImageCanonicalMate] at h ⊢
  erw [Category.id_comp]
  simp only [Functor.map_comp, Category.assoc] at h ⊢
  convert h.symm using 1
end WeilConjectures.PurityFiniteSetting
