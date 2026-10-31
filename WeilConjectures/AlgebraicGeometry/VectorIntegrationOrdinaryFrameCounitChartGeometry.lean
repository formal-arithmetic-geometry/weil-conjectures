/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityDiagonalDualizingData

/-! # The actual frame map lies over the bundle projection

Source: orientation-charts proof Step 1.
Expand the coordinate map. The affine-space projection equation and
trivializationMap_spec identify its composite with the restricted bundle projection;
morphismRestrict_ι then gives the asserted equality over S. This proof is uniform
in the rank and also applies to the empty open.
(blueprint: new-lem-pur-vector-integration-ordinary-frame-counit-chart-geometry).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- The inverse-frame chart has the expected composite over the base.

Source: blueprint latest, sec-smooth-purity/sk-prop-sp-orientation,
orientation-charts proof Step 1. Expand the zero-section trivialization and the
affine-space map. The pullback equation for the affine-space map, the defining
equation of the trivialization, and `AffineSpace.map_over` identify the composite
with the restricted bundle projection. This is the Cartesian chart equation; it
uses no integration or locality comparison and remains valid in rank zero and on
an empty open.
(blueprint: new-lem-pur-vector-integration-ordinary-frame-counit-chart-geometry). -/
theorem vectorIntegration_ordinary_frame_counit_chart_geometry
    (P : PurityFiniteSetting.{u})
    (S : Scheme.{u}) [IsAffine S] (aS : S ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aS] [QuasiCompact aS]
    (d : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d] :
    letI := isNoetherian_of_locallyOfFiniteType aS
    letI := (Etale.vectorIntegration_geometry S d F).1
    letI := (Etale.vectorIntegration_geometry S d F).2.1
    letI := isNoetherian_of_locallyOfFiniteType
      (VectorBundleZeroSection.π S d F ≫ aS)
    letI : HasCompactification (VectorBundleZeroSection.π S d F) := inferInstance
    letI := affineTraceNoetherian S d
    ∀ (U : S.Opens) [IsAffine U.toScheme]
      (frame : VectorBundleZeroSection.Trivialization S d F U),
      let p := VectorBundleZeroSection.π S d F
      let W := p ⁻¹ᵁ U
      let v0 := VectorBundleZeroSection.trivializationMap S d F U frame ≫
        AffineSpace.map (ULift.{u} (Fin d)) U.ι ≫
          (affineTraceAffineSpaceIso S d).inv
      v0 ≫ affineTraceProjection S d = W.ι ≫ p := by
  classical
  letI := isNoetherian_of_locallyOfFiniteType aS
  letI := (Etale.vectorIntegration_geometry S d F).1
  letI := (Etale.vectorIntegration_geometry S d F).2.1
  letI := isNoetherian_of_locallyOfFiniteType
    (VectorBundleZeroSection.π S d F ≫ aS)
  letI : HasCompactification (VectorBundleZeroSection.π S d F) := inferInstance
  letI := affineTraceNoetherian S d
  intro U hAffine frame
  dsimp only
  let p := VectorBundleZeroSection.π S d F
  let W := p ⁻¹ᵁ U
  let v := VectorBundleZeroSection.trivializationMap S d F U frame ≫
    AffineSpace.map (ULift.{u} (Fin d)) U.ι ≫
      (affineTraceAffineSpaceIso S d).inv
  have hp : (affineTraceAffineSpaceIso S d).inv ≫ affineTraceProjection S d =
      AffineSpace (ULift.{u} (Fin d)) S ↘ S := by
    apply (cancel_epi (affineTraceAffineSpaceIso S d).hom).mp
    simp only [Iso.hom_inv_id_assoc]
    exact (AffineSpace.homOfVector_over _ _).symm
  have hw : v ≫ affineTraceProjection S d = W.ι ≫ p := by
    dsimp only [v]
    simp only [Category.assoc, hp, AffineSpace.map_over]
    rw [← Category.assoc,
      (VectorBundleZeroSection.trivializationMap_spec S d F U frame).2.1,
      morphismRestrict_ι]
  exact hw

end WeilConjectures.PurityFiniteSetting
