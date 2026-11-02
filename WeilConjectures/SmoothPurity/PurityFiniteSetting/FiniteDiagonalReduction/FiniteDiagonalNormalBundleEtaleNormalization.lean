/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.DiagonalDncChartNormalization
public import WeilConjectures.AlgebraicGeometry.NoetherianSectionSpecialization.NoetherianEtaleSectionSpecialization

/-! # Exceptional normalization of the normal-bundle section presentation

Source: blueprint latest, smooth orientation charts and coefficient reduction.
(blueprint: lem-pur-finite-diagonal-normal-bundle-etale-normalization). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
open Etale.FiniteSmoothPurity

variable (P : PurityFiniteSetting.{u})
variable {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
variable [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
variable [SmoothOfRelativeDimension d f]
variable (aY : Y ⟶ Spec (.of P.field.k))
variable [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]

/-- The normalized source-etale section restriction along the homogeneous cone
model is the exceptional base-change map, with the identity-base pullback removed.
Source: blueprint latest, smooth orientation charts Step 3, the normalized exceptional
adjunction mate, and reduction compatibilities (3).
(blueprint: lem-pur-finite-diagonal-normal-bundle-etale-normalization).

Proof: the cone model is an isomorphism over the base and preserves the augmentation,
so its square over the identity of the base is Cartesian. The source-etale locality
isomorphism is characterized by the compact-support compositor and its counit equation.
The exceptional base-change map is the mate of the same compact-support exchange.
Normalize the identity-base compact-support exchange by its identity law. Transposing
under the bundle compact-support adjunction gives the same counit composite for both
maps. Injectivity of the adjunction hom equivalence identifies them. Pull to the zero
section and use its equation with the cone augmentation. Pullback associativity and
the identity inverse-image comparison cancel the two section compositors, giving
exactly the displayed equation. The homogeneous model fixes the projection and
augmentation even at rank zero, and the mate equations also hold on an empty base. -/
theorem finiteDiagonalNormalBundleEtaleNormalization :
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
    rP.hom =
      (Etale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) X).inv.app
          (Etale.sectionInvariant P.Coefficient π z) ≫
        Etale.NoetherianSectionSpecialization.sectionMap P.Coefficient π
          (VectorBundleZeroSection.π X d F) (𝟙 X) (chartNormalModel d f).hom
          (IsPullback.of_horiz_isIso ⟨by
            exact ((chartNormal_model_exists d f).exists.choose_spec.2.1).trans
              (Category.comp_id _).symm⟩) z (VectorBundleZeroSection.zero X d F)
          (by
            exact ((chartNormal_model_exists d f).exists.choose_spec.2.2).trans
              (Category.id_comp _).symm) := by
  sorry

end WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
