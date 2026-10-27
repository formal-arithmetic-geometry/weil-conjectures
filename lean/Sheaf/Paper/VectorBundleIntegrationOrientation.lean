/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E4
-/
module

public import Sheaf.Paper.PurityDiagonalDualizingData
import Sheaf.Paper.VectorIntegrationOrdinaryFrameCounit
import all Sheaf.Paper.DiagonalOrdinaryOrientationRigidity
import Sheaf.AlgebraicGeometry.VectorBundleFiniteTypeFrames
import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
import Sheaf.AlgebraicGeometry.OrdinaryFiniteTwistTransportUniqueness

/-! # Integration and normalized ordinary vector-bundle orientations

Source: blueprint latest, sec-smooth-purity/sk-prop-sp-orientation,
sk-prop-sp-orientation-charts.proof.md, Step 4.
(blueprint: lem-pur-vector-bundle-integration-orientation).

The bundle model calculation precedes transport along a presentation of the
normal cone.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

attribute [local instance] Sheaf.monoidalCategory

attribute [local irreducible] VectorBundleZeroSection.scheme VectorBundleZeroSection.π
  Etale.rightDerivedLowerShriek Etale.rightDerivedUpperShriek
  Etale.rightDerivedUpperShriekAdjunction Etale.ordinaryFinitePullback
  Etale.vectorIntegrationBaseCoefficientPullback Etale.vectorBundleIntegration
  diagonalEtaleLocality diagonalAffineMate Functor.mapDerivedCategory

/-- On an affine base, a normalized ordinary orientation of a vector-bundle
projection is inverse to the actual integration adjunct.
Source: blueprint latest, sec-smooth-purity/sk-prop-sp-orientation,
sk-prop-sp-orientation-charts.proof.md, Step 4; the integration normalization in
sk-prop-sp-orientation-vector-bundle.proof.md.
(blueprint: lem-pur-vector-bundle-integration-orientation).

Proof: choose affine opens of the base on which the bundle is free and refine
their inverse images by affine coordinate charts. The defining normalization of
`e` identifies its inverse on each such chart with the pulled-back ordered affine
counit mate, followed by normalized source-etale locality. The chart description
of vector integration is the same ordered affine trace; its exceptional adjunct
has the same locality equation by compact-support base change and mate pasting.
The canonical Tate coefficient pullbacks identify the two sources. Thus the two
maps agree on every frame. Compose their difference with `e` and remove the common
shift by twice the rank. The Tate coefficient is locally a rank-one sheaf in
degree zero, so faithfulness of the single-complex embedding and sheaf Hom descent
make this difference zero globally. Restore the shift and cancel `e`. The ordered
trace at rank zero is the identity counit, so this argument includes rank zero;
the empty cover proves the assertion for an empty base. No field-extension or
reducedness hypothesis is used. -/
theorem vectorBundleIntegration_orientation_inv (P : PurityFiniteSetting.{u})
    (S : Scheme.{u}) [IsAffine S] (aS : S ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aS] [QuasiCompact aS]
    (d : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) :
    letI := isNoetherian_of_locallyOfFiniteType aS
    letI := (Etale.vectorIntegration_geometry S d F).1
    letI := (Etale.vectorIntegration_geometry S d F).2.1
    letI := isNoetherian_of_locallyOfFiniteType (VectorBundleZeroSection.π S d F ≫ aS)
    letI : HasCompactification (VectorBundleZeroSection.π S d F) := inferInstance
    ∀ e : P.diagonalOrdinaryDualizing (VectorBundleZeroSection.π S d F) ≅
        P.diagonalTwistEtale (VectorBundleZeroSection.scheme S d F) d,
      P.DiagonalOrientationNormalization d (VectorBundleZeroSection.π S d F) aS e →
      e.inv =
        (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
          P.diagonalExponent_annihilates t (VectorBundleZeroSection.π S d F)
          (P.diagonalExponent_isUnit aS) d).inv ≫
        (Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} P.Coefficient)
          (VectorBundleZeroSection.π S d F)).homEquiv _ _
            (Etale.vectorBundleIntegration P.diagonalExponent
              (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
              P.diagonalExponent_annihilates S (P.diagonalExponent_isUnit aS) d F) := by
  classical
  have := isNoetherian_of_locallyOfFiniteType aS
  have := (Etale.vectorIntegration_geometry S d F).1
  have := (Etale.vectorIntegration_geometry S d F).2.1
  have := isNoetherian_of_locallyOfFiniteType (VectorBundleZeroSection.π S d F ≫ aS)
  have : HasCompactification (VectorBundleZeroSection.π S d F) := inferInstance
  have := affineTraceNoetherian S d
  intro e he
  have hN : 0 < P.diagonalExponent := pow_pos P.coefficients.prime.out.pos P.level
  obtain ⟨t', D, _⟩ := Etale.exists_ordinaryFiniteP1Adjunction P.diagonalExponent hN
    P.Coefficient P.diagonalExponent_annihilates
  have ht : t' = t := Etale.ordinaryFiniteTwistTransport_unique P.Coefficient
    P.diagonalExponent P.diagonalExponent_annihilates t' t
  subst t'
  let N := Etale.canonicalEtaleCompactSupportNormalization P.Coefficient
  let X := VectorBundleZeroSection.scheme S d F
  let p := VectorBundleZeroSection.π S d F
  obtain ⟨c⟩ := base_normal_form P.diagonalExponent hN P.Coefficient
    P.diagonalExponent_annihilates X (P.diagonalExponent_isUnit (p ≫ aS)) d
  let L := (_root_.DerivedCategory.singleFunctor _ 0).obj
    (Scheme.finiteEtaleTateSheaf P.Coefficient P.diagonalExponent X
      P.diagonalExponent_annihilates (d : ℤ))
  have hle : _root_.DerivedCategory.TStructure.t.IsLE (L⟦2 * (d : ℤ)⟧)
      (-(2 * (d : ℤ))) :=
    _root_.DerivedCategory.TStructure.t.isLE_shift L 0 (2 * (d : ℤ)) _ (by omega)
  have hge : _root_.DerivedCategory.TStructure.t.IsGE (L⟦2 * (d : ℤ)⟧)
      (-(2 * (d : ℤ))) :=
    _root_.DerivedCategory.TStructure.t.isGE_shift L 0 (2 * (d : ℤ)) _ (by omega)
  have : (P.diagonalTwistEtale X d).IsLE (-(2 * (d : ℤ))) :=
    _root_.DerivedCategory.TStructure.t.isLE_of_iso c.symm _
  have : (P.diagonalOrdinaryDualizing p).IsGE (-(2 * (d : ℤ))) :=
    _root_.DerivedCategory.TStructure.t.isGE_of_iso (c.symm ≪≫ e.symm) _
  obtain ⟨_, _, _, _, _, _, _, _, n, U, E, _, _, hU, _⟩ :=
    VectorBundleZeroSection.finite_type_frames P.field.k S aS d F
  apply map_eq_of_cover.{u} P.Coefficient
    (fun i : ULift.{u} (Fin n) ↦ p ⁻¹ᵁ (U i.down).1)
    (fun x ↦ by
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hU.ge (Set.mem_univ x))
      exact ⟨⟨i⟩, hi⟩)
    (K := P.diagonalTwistEtale X d) (L := P.diagonalOrdinaryDualizing p)
    (-(2 * (d : ℤ)))
  rintro ⟨i⟩
  let W := p ⁻¹ᵁ (U i).1
  let j := W.ι
  have : IsNoetherian W.toScheme := isNoetherian_of_locallyOfFiniteType j
  have : IsAffine (U i).1.toScheme := (U i).2
  have : IsIso (VectorBundleZeroSection.trivializationMap S d F (U i).1 (E i)) :=
    (VectorBundleZeroSection.trivializationMap_spec S d F (U i).1 (E i)).1
  have : IsOpenImmersion (AffineSpace.map (ULift.{u} (Fin d)) (U i).1.ι) :=
    MorphismProperty.of_isPullback
      (AffineSpace.isPullback_map (n := ULift.{u} (Fin d)) (U i).1.ι).flip
      (inferInstance : IsOpenImmersion (U i).1.ι)
  let v := VectorBundleZeroSection.trivializationMap S d F (U i).1 (E i) ≫
    AffineSpace.map (ULift.{u} (Fin d)) (U i).1.ι ≫
      (affineTraceAffineSpaceIso S d).inv
  have : Etale v := inferInstance
  have : IsSeparated v := inferInstance
  have : LocallyOfFiniteType v := inferInstance
  have : QuasiCompact v := inferInstance
  have hp : (affineTraceAffineSpaceIso S d).inv ≫ affineTraceProjection S d =
      AffineSpace (ULift.{u} (Fin d)) S ↘ S := by
    apply (cancel_epi (affineTraceAffineSpaceIso S d).hom).mp
    simp only [Iso.hom_inv_id_assoc]
    exact (AffineSpace.homOfVector_over _ _).symm
  have w : v ≫ affineTraceProjection S d = j ≫ p := by
    dsimp only [v]
    simp only [Category.assoc, hp, AffineSpace.map_over]
    rw [← Category.assoc,
      (VectorBundleZeroSection.trivializationMap_spec S d F (U i).1 (E i)).2.1,
      morphismRestrict_ι]
  have : HasCompactification (j ≫ p) := inferInstance
  have : HasCompactification (v ≫ affineTraceProjection S d) := by
    rw [w]
    infer_instance
  apply (cancel_mono (P.diagonalEtaleLocality N j p).hom).mp
  exact (he t D N W.toScheme j v w).trans
    (P.vectorIntegration_ordinary_frame_counit S aS d F t D N (U i).1 (E i)
      v rfl w).symm

end WeilConjectures.PurityFiniteSetting
