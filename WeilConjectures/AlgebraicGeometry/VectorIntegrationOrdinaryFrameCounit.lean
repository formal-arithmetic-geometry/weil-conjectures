/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityDiagonalDualizingData
import WeilConjectures.AlgebraicGeometry.VectorIntegrationOrdinaryFrameCounitChartGeometry
import WeilConjectures.AlgebraicGeometry.VectorIntegrationFrameAdjointApex
import WeilConjectures.AlgebraicGeometry.AffineCounitBaseChangeApex
import WeilConjectures.AlgebraicGeometry.EtaleLocalityCartesianExchange
import WeilConjectures.AlgebraicGeometry.StandardAffineCounitCoordinateSquare

/-! # Ordinary integration adjunct in a linear frame

Source: blueprint latest, sec-smooth-purity/sk-prop-sp-orientation,
sk-prop-sp-orientation-charts.proof.md, Step 4; the affine-frame normalization
of vector integration in sec-smooth-purity/sk-prop-an/def-amb-vector-integration.
(blueprint: lem-route-vector-integration-ordinary-frame-counit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- In one linear frame the actual ordinary vector integration adjunct is the
ordered affine counit mate, with the specified source-etale locality comparisons.
There is no orientation input and no global equality or descent conclusion.
Source: blueprint latest, orientation-charts proof Step 4, and vector integration's
inverse-frame normalization and the affine trace base-change formula.
(blueprint: lem-route-vector-integration-ordinary-frame-counit).

Proof in words:
1. Put p=π_F, W=p⁻¹U, j=W.ι, and let a be the actual frame map to the
coordinate tower over U. The inverse frame c satisfies a≫c=j. The coordinate
square identifies the displayed affine map with a≫affineTraceMap(U.ι,d).
The restriction square and the tower base-change square give both Cartesian
squares with the same projection r=a≫π_U.
2. Normalize vectorIntegration_frameAdjoint with the ordered Tate pullback
square and affineCounitMate_unitChange. It gives c*(I) B_c=C_c M_U, where
I=C_p.inv followed by the actual integration adjunct. Pull back along a.
Cartesian-apex pasting and coefficient composition give
(F) j*(I) B_j=C_j C_a.inv a*(M_U) J_a.
3. Apply standardAffineCounit_towerBaseChange along U.ι. Its coefficient
base-change formula, the ordered Tate square and affine mate unit conversion
give b*(M_S) B_b=C_b M_U. Pull back along a and use the same apex-pasting and
coefficient-composition equations to obtain
(A) v*(M_S) B_v=C_v C_a.inv a*(M_U) J_a.
4. Factor source locality into inverse rho followed by inverse exceptional
composition. The horizontal double-counit compositor formula identifies the
actual exchange mate with this source locality followed by equality transport
and the target-open factor. For both Cartesian squares that last factor is
the same. The calculation holds at every unbounded complex; evaluate at the
fixed coefficient unit. Equality transport for w gives the common-tail formula
B_v=L_v congr(w) L_j.inv B_j.
5. Open exceptional base change makes B_j invertible. Define
H=L_j.symm followed by asIso(B_j), so B_j=L_j H and B_v=L_v congr(w) H.
Precompose (A) by C_j C_v.inv, cancel C_v.inv C_v, and substitute (F).
Substitute the two locality formulas and cancel H on the right. This gives
exactly the equation below. No evaluation counit is cancelled.
6. All coefficient recursions, Cartesian squares and comparisons are defined
for d=0 and for empty U; the same equations and isomorphism cancellations apply.
-/
theorem vectorIntegration_ordinary_frame_counit (P : PurityFiniteSetting.{u})
    (S : Scheme.{u}) [IsAffine S] (aS : S ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aS] [QuasiCompact aS]
    (d : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T]
      (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t T hT)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :
    letI := isNoetherian_of_locallyOfFiniteType aS
    letI := (Etale.vectorIntegration_geometry S d F).1
    letI := (Etale.vectorIntegration_geometry S d F).2.1
    letI := isNoetherian_of_locallyOfFiniteType (VectorBundleZeroSection.π S d F ≫ aS)
    letI : HasCompactification (VectorBundleZeroSection.π S d F) := inferInstance
    letI := affineTraceNoetherian S d
    ∀ (U : S.Opens) [IsAffine U.toScheme]
      (frame : VectorBundleZeroSection.Trivialization S d F U),
      let p := VectorBundleZeroSection.π S d F
      let W := p ⁻¹ᵁ U
      letI := isNoetherian_of_locallyOfFiniteType W.ι
      ∀ (v : W.toScheme ⟶ affineTraceTower S d)
        [Etale v] [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v]
        (_hv : v = VectorBundleZeroSection.trivializationMap S d F U frame ≫
          AffineSpace.map (ULift.{u} (Fin d)) U.ι ≫ (affineTraceAffineSpaceIso S d).inv)
        (w : v ≫ affineTraceProjection S d = W.ι ≫ p),
        letI : HasCompactification (W.ι ≫ p) := inferInstance
        letI : HasCompactification (v ≫ affineTraceProjection S d) := by
          rw [w]
          infer_instance
        (Etale.ordinaryFinitePullback P.Coefficient W.ι).map
            ((Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
              P.diagonalExponent_annihilates t p (P.diagonalExponent_isUnit aS) d).inv ≫
            (Etale.rightDerivedUpperShriekAdjunction P.Coefficient
              p).homEquiv _ _
                (Etale.vectorBundleIntegration P.diagonalExponent
                  (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
                  P.diagonalExponent_annihilates S (P.diagonalExponent_isUnit aS) d F)) ≫
            (P.diagonalEtaleLocality N W.ι p).hom =
          (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
            P.diagonalExponent_annihilates t W.ι (P.diagonalExponent_isUnit (p ≫ aS)) d).hom ≫
          (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
            P.diagonalExponent_annihilates t v
              (affineTraceInvertible P.diagonalExponent S (P.diagonalExponent_isUnit aS) d)
                d).inv ≫
          (Etale.ordinaryFinitePullback P.Coefficient v).map
            (P.diagonalAffineMate t D S (P.diagonalExponent_isUnit aS) d) ≫
          (P.diagonalEtaleLocality N v (affineTraceProjection S d)).hom ≫
          (P.diagonalDualizingCongr w).hom  := by
  classical
  letI := isNoetherian_of_locallyOfFiniteType aS
  letI := (Etale.vectorIntegration_geometry S d F).1
  letI := (Etale.vectorIntegration_geometry S d F).2.1
  letI := isNoetherian_of_locallyOfFiniteType
    (VectorBundleZeroSection.π S d F ≫ aS)
  letI : HasCompactification (VectorBundleZeroSection.π S d F) := inferInstance
  letI := affineTraceNoetherian S d
  let p := VectorBundleZeroSection.π S d F
  intro U hAffine frame
  dsimp only
  let W := p ⁻¹ᵁ U
  let v0 := VectorBundleZeroSection.trivializationMap S d F U frame ≫
    AffineSpace.map (ULift.{u} (Fin d)) U.ι ≫
      (affineTraceAffineSpaceIso S d).inv
  letI : IsIso (VectorBundleZeroSection.trivializationMap S d F U frame) :=
    (VectorBundleZeroSection.trivializationMap_spec S d F U frame).1
  letI : IsOpenImmersion
      (AffineSpace.map (ULift.{u} (Fin d)) U.ι) :=
    MorphismProperty.of_isPullback
      (AffineSpace.isPullback_map (n := ULift.{u} (Fin d)) U.ι).flip
      (inferInstance : IsOpenImmersion U.ι)
  letI : Etale v0 := by dsimp only [v0]; infer_instance
  letI : IsSeparated v0 := by dsimp only [v0]; infer_instance
  letI : LocallyOfFiniteType v0 := by dsimp only [v0]; infer_instance
  letI : QuasiCompact v0 := by dsimp only [v0]; infer_instance
  intro v _ _ _ _ hv w
  subst v
  letI := isNoetherian_of_locallyOfFiniteType W.ι
  have w0 : v0 ≫ affineTraceProjection S d = W.ι ≫ p := by
    exact vectorIntegration_ordinary_frame_counit_chart_geometry P S aS d F U frame
  letI := isNoetherian_of_locallyOfFiniteType U.ι
  letI := affineTraceNoetherian U.toScheme d
  let a := VectorBundleZeroSection.trivializationMap S d F U frame ≫
    (affineTraceAffineSpaceIso U.toScheme d).inv
  letI : IsIso a := by dsimp only [a]; infer_instance
  let r := a ≫ affineTraceProjection U.toScheme d
  letI : HasCompactification r := inferInstance
  let b := (affineTraceAffineSpaceIso U.toScheme d).hom ≫
    AffineSpace.map (ULift.{u} (Fin d)) U.ι ≫ (affineTraceAffineSpaceIso S d).inv
  have hb : b = affineTraceMap U.ι d := by
    apply (cancel_mono (affineTraceAffineSpaceIso S d).hom).mp
    simpa only [b, Category.assoc, Iso.inv_hom_id, Category.comp_id] using
      (Etale.standardAffineCounit_coordinateSquare U.ι d).symm
  have hv0 : a ≫ b = v0 := by
    simp only [a, b, v0, Category.assoc, Iso.inv_hom_id_assoc]
  have hr : r = p ∣_ U := by
    apply (cancel_mono U.ι).mp
    rw [morphismRestrict_ι]
    calc
      r ≫ U.ι = (a ≫ b) ≫ affineTraceProjection S d := by
        simp only [r, hb, Category.assoc, (affineTraceMap_isPullback U.ι d).w]
      _ = W.ι ≫ p := by rw [hv0]; exact w0
  have qj : IsPullback W.ι r p U.ι := by
    rw [hr]
    exact (isPullback_morphismRestrict p U).flip
  have qv : IsPullback v0 r (affineTraceProjection S d) U.ι := by
    have h := (affineTraceMap_isPullback U.ι d).of_iso'
      (asIso a) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (fst' := v0) (snd' := r) (f' := affineTraceProjection S d) (g' := U.ι)
      (by simpa only [asIso_hom, Iso.refl_hom, Category.comp_id, ← hb] using hv0)
      (by simp only [asIso_hom, Iso.refl_hom, Category.comp_id, r])
      (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id])
      (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id])
    exact h
  let I := (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient
      P.diagonalExponent P.diagonalExponent_annihilates t p
      (P.diagonalExponent_isUnit aS) d).inv ≫
    (Etale.rightDerivedUpperShriekAdjunction P.Coefficient p).homEquiv _ _
      (Etale.vectorBundleIntegration P.diagonalExponent
        (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
        P.diagonalExponent_annihilates S (P.diagonalExponent_isUnit aS) d F)
  let Cj := Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient
    P.diagonalExponent P.diagonalExponent_annihilates t W.ι
    (P.diagonalExponent_isUnit (p ≫ aS)) d
  let Cv := Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient
    P.diagonalExponent P.diagonalExponent_annihilates t v0
    (affineTraceInvertible P.diagonalExponent S (P.diagonalExponent_isUnit aS) d) d
  let R : Etale.affineLinearBaseCoefficient P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates W.toScheme d ⟶ P.diagonalOrdinaryDualizing r :=
    (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient
      P.diagonalExponent P.diagonalExponent_annihilates t a
      (affineTraceInvertible P.diagonalExponent U.toScheme
        (P.diagonalExponent_isUnit (U.ι ≫ aS)) d) d).inv ≫
    (Etale.ordinaryFinitePullback P.Coefficient a).map
      (P.diagonalAffineMate t D U.toScheme
        (P.diagonalExponent_isUnit (U.ι ≫ aS)) d) ≫
    P.ordinaryCoefficientApexComparison (asIso a)
      (affineTraceProjection U.toScheme d)
  let Bj := P.ordinaryCoefficientDualizingExchange qj
  let Bv := P.ordinaryCoefficientDualizingExchange qv
  have hF : (Etale.ordinaryFinitePullback P.Coefficient W.ι).map I ≫ Bj =
      Cj.hom ≫ R := by
    exact P.vectorIntegration_frame_adjoint_apex S aS d F t D U frame qj
  have hA : (Etale.ordinaryFinitePullback P.Coefficient v0).map
      (P.diagonalAffineMate t D S (P.diagonalExponent_isUnit aS) d) ≫ Bv =
      Cv.hom ≫ R := by
    have h := P.affineCounit_baseChange_apex t D S U.toScheme W.toScheme U.ι
      (P.diagonalExponent_isUnit aS) d (asIso a)
    dsimp only [asIso_hom] at h
    rw [hv0] at h
    exact h qv
  have hL := P.etaleLocality_cartesian_exchange N p (affineTraceProjection S d)
    U.ι r W.ι v0 qj qv w
  letI : IsIso Bj := P.ordinaryCoefficientDualizingExchange_isIso qj
  have he : (Etale.ordinaryFinitePullback P.Coefficient W.ι).map I ≫ Bj =
      Cj.hom ≫ Cv.inv ≫ (Etale.ordinaryFinitePullback P.Coefficient v0).map
        (P.diagonalAffineMate t D S (P.diagonalExponent_isUnit aS) d) ≫ Bv := by
    rw [hF, hA]
    simp only [Iso.inv_hom_id_assoc]
  let H := (P.diagonalEtaleLocality N W.ι p).symm ≪≫ asIso Bj
  have hLj : Bj = (P.diagonalEtaleLocality N W.ι p).hom ≫ H.hom := by
    simp only [H, Iso.trans_hom, Iso.symm_hom, asIso_hom, Iso.hom_inv_id_assoc]
  have hLv : Bv = (P.diagonalEtaleLocality N v0 (affineTraceProjection S d)).hom ≫
      (P.diagonalDualizingCongr w).hom ≫ H.hom := by
    simpa only [H, Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc] using hL
  apply (cancel_mono H.hom).mp
  calc
    _ = (Etale.ordinaryFinitePullback P.Coefficient W.ι).map I ≫ Bj := by
      rw [Category.assoc, ← hLj]
    _ = _ := he
    _ = _ := by
      rw [hLv]
      simp only [Category.assoc, Cj, Cv, v0, W, p]

end WeilConjectures.PurityFiniteSetting
