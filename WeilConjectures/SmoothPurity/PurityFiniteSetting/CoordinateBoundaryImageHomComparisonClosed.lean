/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.PurityAffineLineBoundaryRealization
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedHomPullback
public import WeilConjectures.AlgebraicGeometry.SupportedConstantNormalization.SupportedConstantExchangeNormalization

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.RetractedSupport

/-! # Normalized closed exchange of a site support transport

Every comparison-site support transport for a zero section has the canonical closed
exchange: `site_normalization` characterizes `gamma` by its restriction equation.
(blueprint: lem-pur-coordinate-boundary-image-hom-comparison-closed-prefix).
-/

/- The four private lemmas below are verbatim copies of the private constant-section
evaluations of `Sheaf.Paper.SupportedHomPullback` (private there, so not importable). -/
namespace AlgebraicGeometry.CoordinateBoundaryImageHomComparisonClosed

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
end AlgebraicGeometry.CoordinateBoundaryImageHomComparisonClosed

namespace WeilConjectures.PurityFiniteSetting

open AlgebraicGeometry.CoordinateBoundaryImageHomComparisonClosed in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The closed exchange of a site transport is fixed by the normalized constant
restriction equation.
Source: current blueprint, cor-pur-affine-space-zero-section-purity.proof.md,
finite etale-origin transport paragraph; Milne, Section 9
(blueprint: lem-pur-coordinate-boundary-image-hom-comparison-closed-prefix).
Proof: `constantIso_spec` and the comparison constant-unit specification have the same
adjoint, so `v.constantIso` is the comparison unit isomorphism. The etale constant
restriction of the support pair is `restriction false`, and the pro-etale one followed by
the closed image of the unit isomorphism is `restriction true`. Hence `closedIso_spec`
says that `v.closedIso.hom` followed by that closed image satisfies the restriction
equation of `site_normalization`, whose uniqueness clause identifies it with `gamma`;
cancel the unit isomorphism. -/
theorem coordinateBoundaryImageHomComparison_closed_prefix
    (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (v : siteSupportHomTransport P (zeroSection T)) :
    v.closedIso.hom =
      AlgebraicGeometry.SupportedConstantNormalization.gamma P.Coefficient
          (zeroSection T) ≫
        (ProEtale.lowerStar (Modules P) (zeroSection T)).map
          (ProEtale.comparisonUpperStarUnitIso P.Coefficient T).inv := by
  let := Scheme.isContinuous_toProEt (Line T)
  let : (MorphismProperty.Over.pullback @Etale ⊤ (zeroSection T)).IsContinuous
      (Line T).smallEtaleTopology T.smallEtaleTopology :=
    Etale.isContinuous_overPullback (zeroSection T)
  have hn := SupportedConstantNormalization.site_normalization P (zeroSection T)
  have hc : v.constantIso.hom =
      (ProEtale.comparisonUpperStarUnitIso P.Coefficient (Line T)).hom := by
    apply ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} P.Coefficient)
      (Line T)).homEquiv _ _).injective
    exact v.constantIso_spec.trans (supportHomComparisonConstantIso_spec (Line T)).symm
  have hs := v.closedIso_spec
  rw [hc] at hs
  have hd := hn.2.2.2.2.2.2 (v.closedIso.hom ≫
      (ProEtale.lowerStar (Modules P) (zeroSection T)).map
        (ProEtale.comparisonUpperStarUnitIso P.Coefficient T).hom) (by
    change (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) (Line T)).map
        ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient)
          (zeroSection T)).homEquiv _ _
          ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} P.Coefficient)
            (zeroSection T)).app (ModuleCat.of P.Coefficient P.Coefficient)).hom) ≫ _ = _
    erw [supportHomEtaleConstantIso_spec (zeroSection T)]
    rw [← Category.assoc]
    erw [hs]
    rw [Category.assoc]
    congr 1
    change (supportHomConstantDirectImage (A := P.Coefficient)
        (Scheme.ProEt.topology (Line T))
        (Scheme.ProEt.topology T) (MorphismProperty.Over.pullback @WeaklyEtale ⊤
          (zeroSection T)) ≫
        (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) (zeroSection T)).map
          (ProEtale.comparisonUpperStarUnitIso P.Coefficient T).inv) ≫
        (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) (zeroSection T)).map
          (ProEtale.comparisonUpperStarUnitIso P.Coefficient T).hom = _
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id]
    rfl)
  rw [← hd, Category.assoc, ← Functor.map_comp, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.comp_id]

end WeilConjectures.PurityFiniteSetting
