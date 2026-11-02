/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteDiagonalReduction.FiniteDiagonalReductionComparisons
import WeilConjectures.SixFunctors.DncCoefficientTransport.SectionScalarBaseChange
import WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarPullbackIdentityNormalization
import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteDiagonalReduction.FiniteDiagonalNormalBundleEtaleNormalization

/-! # Coefficient naturality of the geometric normal-bundle presentation

Source: blueprint latest, smooth orientation charts and coefficient reduction.
(blueprint: lem-pur-finite-diagonal-normal-bundle-presentation-scalar). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
open Etale.FiniteSmoothPurity

attribute [local implicit_reducible] ordinaryScalar Scheme.Modules TopCat.Sheaf

variable (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
variable {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
variable [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
variable [SmoothOfRelativeDimension d f]
variable (aY : Y ⟶ Spec (.of P.field.k))
variable [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]

/-- The ordinary geometric normal-cone-to-bundle section presentation respects
coefficient reduction, before site comparison or integration is composed.
Source: blueprint latest, reduction compatibilities proof (3), normal-bundle factor.
(blueprint: lem-pur-finite-diagonal-normal-bundle-presentation-scalar).

Proof: the homogeneous associated-graded-to-symmetric-algebra isomorphism is
independent of the coefficient ring and preserves the augmentation. Its exceptional
section mate is a composite of pullback compositors, exceptional counits and the
coefficient-unit identification. Identify the canonical source-etale locality mate
with the normalized exceptional section base-change mate for this isomorphism square.
Apply section_scalar_base_change and cancel the identity-base pullback constraints;
scalar-pullback unit coherence identifies the remaining coefficient-unit arrows.
Pasting gives the displayed ordinary section square. This uses derived scalar
extension and needs no quotient flatness. The same identity-base constraints also
cover rank zero and the empty scheme. -/
theorem finiteDiagonalNormalBundlePresentationScalar :
    letI := P.noetherian (f ≫ aY)
    letI := (chartDiagonalNormalBundle d f).1
    let F := ConormalGradedAlgebra.piece (pullback.diagonal f) 1
    let π := Scheme.Hom.normalConeProj (pullback.fst f f) (pullback.diagonal f)
    let z := Scheme.Hom.normalConeZeroSection (pullback.diagonal f)
    letI := Dnc.normalQuasiCompact d (pullback.fst f f)
      (pullback.diagonal f) (pullback.diagonal_fst f)
    letI := Dnc.normalCompactifiable P d (pullback.fst f f) (f ≫ aY)
      (pullback.diagonal f) (pullback.diagonal_fst f)
    letI := P.noetherian (π ≫ f ≫ aY)
    letI := (Etale.vectorIntegration_geometry X d F).1
    letI := (Etale.vectorIntegration_geometry X d F).2.1
    letI := Dnc.compactifiable P (VectorBundleZeroSection.π X d F) (f ≫ aY)
    letI := P.noetherian (VectorBundleZeroSection.π X d F ≫ f ≫ aY)
    let rP := P.chartSectionEtaleRestriction
      (Etale.canonicalEtaleCompactSupportNormalization P.Coefficient)
      (chartNormalModel d f).hom π (VectorBundleZeroSection.π X d F)
      (chartNormal_model_exists d f).exists.choose_spec.2.1 z
      (VectorBundleZeroSection.zero X d F)
      (chartNormal_model_exists d f).exists.choose_spec.2.2
    let rQ := (P.finiteReductionSetting m hm).chartSectionEtaleRestriction
      (Etale.canonicalEtaleCompactSupportNormalization
        (P.finiteReductionSetting m hm).Coefficient)
      (chartNormalModel d f).hom π (VectorBundleZeroSection.π X d F)
      (chartNormal_model_exists d f).exists.choose_spec.2.1 z
      (VectorBundleZeroSection.zero X d F)
      (chartNormal_model_exists d f).exists.choose_spec.2.2
    (ordinaryScalar (quotient P m hm hmn) X).map rP.hom ≫
      DncCoefficientTransport.sectionMap (quotient P m hm hmn)
        (VectorBundleZeroSection.π X d F) (VectorBundleZeroSection.zero X d F) =
    DncCoefficientTransport.sectionMap (quotient P m hm hmn) π z ≫ rQ.hom := by
  let _ := P.noetherian (f ≫ aY)
  let _ := (chartDiagonalNormalBundle d f).1
  let F := ConormalGradedAlgebra.piece (pullback.diagonal f) 1
  let π := Scheme.Hom.normalConeProj (pullback.fst f f) (pullback.diagonal f)
  let z := Scheme.Hom.normalConeZeroSection (pullback.diagonal f)
  let πE := VectorBundleZeroSection.π X d F
  let zE := VectorBundleZeroSection.zero X d F
  let _ := Dnc.normalQuasiCompact d (pullback.fst f f)
    (pullback.diagonal f) (pullback.diagonal_fst f)
  let _ := Dnc.normalCompactifiable P d (pullback.fst f f) (f ≫ aY)
    (pullback.diagonal f) (pullback.diagonal_fst f)
  let _ := P.noetherian (π ≫ f ≫ aY)
  let _ := (Etale.vectorIntegration_geometry X d F).1
  let _ := (Etale.vectorIntegration_geometry X d F).2.1
  let _ := Dnc.compactifiable P πE (f ≫ aY)
  let _ := P.noetherian (πE ≫ f ≫ aY)
  let e := chartNormalModel d f
  let φ := quotient P m hm hmn
  have w : e.hom ≫ π = πE :=
    (chartNormal_model_exists d f).exists.choose_spec.2.1
  have hz : zE ≫ e.hom = (𝟙 X) ≫ z := by
    exact (chartNormal_model_exists d f).exists.choose_spec.2.2.trans
      (Category.id_comp _).symm
  have sq : IsPullback e.hom πE π (𝟙 X) :=
    IsPullback.of_horiz_isIso ⟨by rw [w, Category.comp_id]⟩
  let _ : SmoothOfRelativeDimension d π :=
    (Scheme.Hom.normalConeData d (pullback.diagonal_fst f)).smoothOfRelativeDimension_proj
  have hB : (P.diagonalExponent : (P.finiteReductionSetting m hm).Coefficient) = 0 := by
    rw [← map_natCast φ, P.diagonalExponent_annihilates, map_zero]
  have h := (DncCoefficientTransport.section_scalar_base_change φ P.diagonalExponent
    (pow_pos P.coefficients.prime.out.pos P.level)
    P.diagonalExponent_annihilates hB (P.diagonalExponent_isUnit (f ≫ aY)) π d).2
    πE (𝟙 X) e.hom sq z zE hz
  let C := Etale.sectionInvariant P.Coefficient π z
  let D := Etale.sectionInvariant (P.finiteReductionSetting m hm).Coefficient π z
  let eA := Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) X
  let eB := Etale.leftDerivedUpperStarId
    (ModuleCat.{u + 1} (P.finiteReductionSetting m hm).Coefficient) X
  let S := ordinaryScalar φ X
  let r := (Etale.scalarPullbackIso φ (𝟙 X)).app C
  let c := DncCoefficientTransport.sectionMap φ π z
  have hi : S.map (eA.inv.app C) ≫ r.inv = eB.inv.app (S.obj C) := by
    apply (cancel_mono (eB.hom.app (S.obj C))).1
    have hu := (Etale.etaleScalarPullbackIdentityNormalization φ X).2.2 C
    change r.hom ≫ S.map (eA.hom.app C) = eB.hom.app (S.obj C) at hu
    conv_lhs =>
      rw [Category.assoc, ← hu, Iso.inv_hom_id_assoc, ← S.map_comp,
        Iso.inv_hom_id_app, S.map_id]
    exact (eB.inv_hom_id_app _).symm
  have hn := eB.inv.naturality c
  change c ≫ eB.inv.app D = eB.inv.app (S.obj C) ≫
    (Etale.upperStar (ModuleCat.{u + 1} (P.finiteReductionSetting m hm).Coefficient)
      (𝟙 X)).leftDerivedFunctor.map c at hn
  dsimp only
  rw [finiteDiagonalNormalBundleEtaleNormalization P d f aY,
    finiteDiagonalNormalBundleEtaleNormalization (P.finiteReductionSetting m hm)
      d f aY]
  symm
  change c ≫ eB.inv.app D ≫ _ = S.map (eA.inv.app C ≫ _) ≫ _
  rw [← Category.assoc, hn, ← hi]
  simp only [Category.assoc, Functor.map_comp]
  exact congrArg (fun q ↦ S.map (eA.inv.app C) ≫ q) h

end WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
