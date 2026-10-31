/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.OrdinaryCoefficientDualizingExchange
public import WeilConjectures.AlgebraicGeometry.CoordinateCounitArrows.CoordinateCounitArrows
import WeilConjectures.SmoothPurity.PurityFiniteSetting.OrdinaryCoefficientCartesianApexFormula
import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationFrameAdjoint
import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationBaseCoefficientComposition
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.AffineCounitMateUnitChange
import WeilConjectures.AlgebraicGeometry.Ordered.OrderedTatePullbackSquare
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit

/-! # The frame-adjoint equation before source locality

Source: orientation-charts proof Step 4, frame-adjoint pullback (F).
Normalize the proved inverse-chart adjunct equation by the ordered coefficient
square and the affine mate unit conversion. Pull back through the frame isomorphism,
use Cartesian-apex pasting, and cancel the last coefficient isomorphism.
(blueprint: new-lem-pur-vector-integration-frame-adjoint-apex).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

attribute [local implicit_reducible] Scheme.Modules

private theorem unit_inv (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] : (OrientationCounit.unitChange P f).inv = 𝟙 _ := by
  unfold OrientationCounit.unitChange
  simp only [Functor.mapIso_inv, Iso.symm_inv]
  have hu : (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} P.Coefficient) Y).hom =
      𝟙 _ := by
    apply (cancel_mono
      (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} P.Coefficient) Y).inv).mp
    rw [Iso.hom_inv_id, Etale.singleFunctorObjUnitIso_inv]
    exact (Category.id_comp _).symm
  erw [hu, CategoryTheory.Functor.map_id]
  rfl


private theorem unit_hom (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] : (OrientationCounit.unitChange P f).hom = 𝟙 _ := by
  apply (cancel_mono (OrientationCounit.unitChange P f).inv).mp
  rw [Iso.hom_inv_id, unit_inv, Category.id_comp]
  rfl

set_option maxHeartbeats 800000 in
-- Kernel checking the fixed derived-category unit identifications needs this budget.
private theorem normalized_frame (P : PurityFiniteSetting.{u})
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    (D : ∀ (Y : Scheme.{u}) [IsNoetherian Y]
      (hY : IsUnit (P.diagonalExponent : Γ(Y, ⊤))),
      Etale.OrdinaryFiniteP1Datum P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t Y hY)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (P.diagonalExponent : Γ(S, ⊤)))
    (d : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (U : S.Opens) [IsNoetherian U.toScheme]
    (frame : VectorBundleZeroSection.Trivialization S d F U) :
    letI := (Etale.vectorIntegration_geometry S d F).1
    letI := (Etale.vectorIntegration_geometry S d F).2.1
    let p := VectorBundleZeroSection.π S d F
    let c := Etale.vectorIntegrationChart S d F U frame
    let q := Etale.vectorIntegrationChart_isPullback S d F U frame
    (Etale.ordinaryFinitePullback P.Coefficient c).map
      ((Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient
        P.diagonalExponent P.diagonalExponent_annihilates t p hS d).inv ≫
      (Etale.rightDerivedUpperShriekAdjunction P.Coefficient p).homEquiv _ _
        (Etale.vectorBundleIntegration P.diagonalExponent
          (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
          P.diagonalExponent_annihilates S hS d F)) ≫
      P.ordinaryCoefficientDualizingExchange q =
    (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient
      P.diagonalExponent P.diagonalExponent_annihilates t c
      (affineTracePullbackInvertible P.diagonalExponent p hS) d).hom ≫
      P.diagonalAffineMate t D U.toScheme
        (affineTracePullbackInvertible P.diagonalExponent U.ι hS) d := by
  letI := (Etale.vectorIntegration_geometry S d F).1
  letI := (Etale.vectorIntegration_geometry S d F).2.1
  intro p c q
  letI := affineTraceNoetherian U.toScheme d
  let hU := affineTracePullbackInvertible P.diagonalExponent U.ι hS
  have ht := Etale.vectorIntegration_frameAdjoint P.diagonalExponent
    (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
    P.diagonalExponent_annihilates t D S hS d F U frame
  have hs := Etale.orderedTatePullbackSquare P.Coefficient P.diagonalExponent
    P.diagonalExponent_annihilates t p (affineTraceProjection U.toScheme d)
    c U.ι q.w.symm hS
    (affineTracePullbackInvertible P.diagonalExponent p hS) hU d
  have hm := P.affineCounitMate_unitChange t D U.toScheme hU d
  simp only [unit_inv, Category.comp_id, Iso.trans_inv] at hm
  simp only [ordinaryCoefficientDualizingExchange, unit_inv, unit_hom,
    Functor.map_comp, CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp,
    Category.assoc]
  erw [ht]
  erw [reassoc_of% hs]
  erw [hm]
  simp only [Category.assoc]


/-- Equation (F), at the restricted base U and before any source-locality map.
Source: orientation-charts proof Step 4.

Proof in words: apply vectorIntegration_frameAdjoint to the inverse frame c.
Normalize its source by the base-coefficient pullback composition square.
The affine mate/unit-change identity identifies its right side with C_c M_U.
Pull back this equality along the actual frame isomorphism a. The Cartesian-apex
formula gives a*(B_c) followed by J_a, with its pullback compositor. Naturality
moves this compositor across I; coefficient composition gives a*(C_c) C_a=C_j.
Cancel C_a to obtain j*(I) B_j=C_j C_a^{-1} a*(M_U) J_a.
This equation involves the affine mate over U only and no locality comparison.
The coefficient composition proof starts with the unit in rank zero and then
tensors with one shifted root line; all identities apply to empty U as well.
(blueprint: new-lem-pur-vector-integration-frame-adjoint-apex). -/
theorem vectorIntegration_frame_adjoint_apex
    (P : PurityFiniteSetting.{u})
    (S : Scheme.{u}) [IsAffine S] (aS : S ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aS] [QuasiCompact aS]
    (d : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T]
      (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t T hT) :
    letI := isNoetherian_of_locallyOfFiniteType aS
    letI := (Etale.vectorIntegration_geometry S d F).1
    letI := (Etale.vectorIntegration_geometry S d F).2.1
    letI := isNoetherian_of_locallyOfFiniteType
      (VectorBundleZeroSection.π S d F ≫ aS)
    letI : HasCompactification (VectorBundleZeroSection.π S d F) := inferInstance
    ∀ (U : S.Opens) [IsAffine U.toScheme]
      (frame : VectorBundleZeroSection.Trivialization S d F U),
      let p := VectorBundleZeroSection.π S d F
      let W := p ⁻¹ᵁ U
      letI := isNoetherian_of_locallyOfFiniteType W.ι
      letI : IsIso (VectorBundleZeroSection.trivializationMap S d F U frame) :=
        (VectorBundleZeroSection.trivializationMap_spec S d F U frame).1
      letI := isNoetherian_of_locallyOfFiniteType U.ι
      letI := affineTraceNoetherian U.toScheme d
      let a := VectorBundleZeroSection.trivializationMap S d F U frame ≫
        (affineTraceAffineSpaceIso U.toScheme d).inv
      letI : IsIso a := by dsimp only [a]; infer_instance
      let r := a ≫ affineTraceProjection U.toScheme d
      letI : HasCompactification r := inferInstance
      ∀ (qj : IsPullback W.ι r p U.ι),
        (Etale.ordinaryFinitePullback P.Coefficient W.ι).map
          ((Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient
            P.diagonalExponent P.diagonalExponent_annihilates t p
            (P.diagonalExponent_isUnit aS) d).inv ≫
          (Etale.rightDerivedUpperShriekAdjunction P.Coefficient p).homEquiv _ _
            (Etale.vectorBundleIntegration P.diagonalExponent
              (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
              P.diagonalExponent_annihilates S (P.diagonalExponent_isUnit aS) d F)) ≫
          P.ordinaryCoefficientDualizingExchange qj =
        (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient
          P.diagonalExponent P.diagonalExponent_annihilates t W.ι
          (P.diagonalExponent_isUnit (p ≫ aS)) d).hom ≫
        (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient
          P.diagonalExponent P.diagonalExponent_annihilates t a
          (affineTraceInvertible P.diagonalExponent U.toScheme
            (P.diagonalExponent_isUnit (U.ι ≫ aS)) d) d).inv ≫
        (Etale.ordinaryFinitePullback P.Coefficient a).map
          (P.diagonalAffineMate t D U.toScheme
            (P.diagonalExponent_isUnit (U.ι ≫ aS)) d) ≫
        P.ordinaryCoefficientApexComparison (asIso a)
          (affineTraceProjection U.toScheme d) := by
  letI := isNoetherian_of_locallyOfFiniteType aS
  letI := (Etale.vectorIntegration_geometry S d F).1
  letI := (Etale.vectorIntegration_geometry S d F).2.1
  letI := isNoetherian_of_locallyOfFiniteType
    (VectorBundleZeroSection.π S d F ≫ aS)
  letI : HasCompactification (VectorBundleZeroSection.π S d F) := inferInstance
  intro U _ frame p W
  letI := isNoetherian_of_locallyOfFiniteType W.ι
  letI : IsIso (VectorBundleZeroSection.trivializationMap S d F U frame) :=
    (VectorBundleZeroSection.trivializationMap_spec S d F U frame).1
  letI := isNoetherian_of_locallyOfFiniteType U.ι
  letI := affineTraceNoetherian U.toScheme d
  intro a
  letI : IsIso a := by dsimp only [a]; infer_instance
  intro r
  letI : HasCompactification r := inferInstance
  intro qj
  let c := Etale.vectorIntegrationChart S d F U frame
  let qc := Etale.vectorIntegrationChart_isPullback S d F U frame
  have hj : W.ι = a ≫ c := by
    simp only [a, c, Etale.vectorIntegrationChart, Category.assoc,
      Iso.inv_hom_id_assoc, IsIso.hom_inv_id_assoc, W, p]
  let q : ChosenCartesianSquare c (affineTraceProjection U.toScheme d) p U.ι :=
    { toCommSq := qc.toCommSq
      isoPullback := qc.isoPullback
      hom_fst := qc.isoPullback_hom_fst
      hom_snd := qc.isoPullback_hom_snd }
  have hB := P.ordinaryCoefficientDualizingExchange_apex q (asIso a) W.ι hj qj
  let I := (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient
    P.diagonalExponent P.diagonalExponent_annihilates t p
    (P.diagonalExponent_isUnit aS) d).inv ≫
    (Etale.rightDerivedUpperShriekAdjunction P.Coefficient p).homEquiv _ _
      (Etale.vectorBundleIntegration P.diagonalExponent
        (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
        P.diagonalExponent_annihilates S (P.diagonalExponent_isUnit aS) d F)
  have hn := (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
    a c W.ι hj).hom.naturality I
  dsimp only [Functor.comp_map] at hn
  have hC := Etale.vectorIntegrationBaseCoefficientPullback_comp P.Coefficient
    P.diagonalExponent P.diagonalExponent_annihilates t a c W.ι hj
    (P.diagonalExponent_isUnit (p ≫ aS))
    (affineTraceInvertible P.diagonalExponent U.toScheme
      (P.diagonalExponent_isUnit (U.ι ≫ aS)) d) d
  let Cj := Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient
    P.diagonalExponent P.diagonalExponent_annihilates t W.ι
    (P.diagonalExponent_isUnit (p ≫ aS)) d
  let Ca := Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient
    P.diagonalExponent P.diagonalExponent_annihilates t a
    (affineTraceInvertible P.diagonalExponent U.toScheme
      (P.diagonalExponent_isUnit (U.ι ≫ aS)) d) d
  have hC' :
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
        a c W.ι hj).hom.app _ ≫
        (Etale.ordinaryFinitePullback P.Coefficient a).map
          (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient
            P.diagonalExponent P.diagonalExponent_annihilates t c
            (P.diagonalExponent_isUnit (p ≫ aS)) d).hom = Cj.hom ≫ Ca.inv := by
    apply (cancel_mono Ca.hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hC
  have hchart := normalized_frame P t D S (P.diagonalExponent_isUnit aS) d F U frame
  change (Etale.ordinaryFinitePullback P.Coefficient W.ι).map I ≫ _ = _
  rw [hB]
  erw [reassoc_of% hn]
  erw [← Functor.map_comp_assoc]
  erw [hchart]
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% hC']
  simp only [Cj, Ca, Etale.ordinaryFinitePullback]

end WeilConjectures.PurityFiniteSetting
