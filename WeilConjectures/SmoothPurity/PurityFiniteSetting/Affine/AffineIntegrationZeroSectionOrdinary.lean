/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.CompositionModelOrientationDefinitions

/-! # The ordinary affine zero-section multiplication equation -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- Ordinary section orientations multiply under the prescribed affine comparison nu.
Source: latest blueprint, composition proof Step 1, direct-sum compatibility and base change;
parent direct-sum-coordinate node, final zero-section pullback step.
(blueprint: lem-pur-affine-integration-zero-section-ordinary).

Proof: apply integration-normalized direct-sum purity to the coordinate bundles. Pull its
unit-coefficient equation back along the total zero section. The first-factor Cartesian
square changes the rank-d factor into the zero-section restriction on B; composition of
inverse images changes the rank-e factor into its zero-section restriction. The definition
of nu is precisely these two inverse-image comparisons, the monoidal pullback constraint,
and pullback of the exceptional compositor. Naturality of the tensor constraint moves the
two ordinary orientations past it. Ordered Tate pullback composition identifies the final
coefficient maps with the inverse of power concatenation. The chart orientation's defining
normalization identifies each restriction with chartSectionOrientation. Rank-zero cases
use the identity adjunction and tensor unitors; the same maps apply over the empty base.
-/
theorem affine_integration_zero_section_ordinary (P : PurityFiniteSetting.{u})
    (B : Scheme.{u}) [IsAffine B] (d e : ℕ)
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB] :
    letI := P.noetherian aB
    letI := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
    letI := DiagonalPasting.affineDimension d B
    letI := DiagonalPasting.affineDimension e B
    letI := DiagonalPasting.affineDimension (d + e) B
    let t := Etale.projectiveLineTraceTransport P.diagonalExponent
      (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
      P.diagonalExponent_annihilates
    DiagonalPasting.nu P.Coefficient P d e B aB ≪≫
        P.chartSectionOrientation (d + e) (DiagonalPasting.pr (d + e) B) aB
          (DiagonalPasting.zero (d + e) B) t =
      compatibleBifunctorIso (Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) B)
        (P.chartSectionOrientation d (DiagonalPasting.pr d B) aB
          (DiagonalPasting.zero d B) t)
        (P.chartSectionOrientation e (DiagonalPasting.pr e B) aB
          (DiagonalPasting.zero e B) t) ≪≫
      (compositionEtalePowerAdd P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates B d e).symm := by
  sorry

end WeilConjectures.PurityFiniteSetting
