/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteCompactificationTranspose.FiniteRingCompactificationTransposeComparison
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothPurityMaps
public import WeilConjectures.AlgebraicGeometry.AffineLinePurity.AffineLinePurityCoordinateMaps
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.DiagonalAffineTrace.DiagonalAffineTraceCoordinates
public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedCounitData
public import WeilConjectures.SixFunctors.Etale.Derived.Identity
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekLocality
public import WeilConjectures.AlgebraicGeometry.Affine.AffineDualizingCoefficient
import all WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedCounitSuccessor

/-! # General coefficient-first ordered affine counit normalization -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor
attribute [local instance] Classical.propDecidable
namespace AlgebraicGeometry.ProEtale.AffineOrderedIntegrationGeneral
open AlgebraicGeometry Scheme
open AlgebraicGeometry.ProEtale.FiniteCompactificationTranspose
open AlgebraicGeometry.ProEtale.VectorIntegrationSite


attribute [local implicit_reducible] AffineOrderedIntegration.proCategory
  AffineOrderedIntegration.etaleCategory Etale.FiniteSmoothPurity.comparison

variable (A : Type (u + 1)) [CommRing A] [Finite A]



private theorem general_reassociation_eq (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (Y : Scheme.{u}) [IsNoetherian Y] (hY : IsUnit (N : Γ(Y, ⊤)))
    (K : Etale.DerivedCategoryModule A Y) (d : ℕ) :
    Etale.OrdinaryAffineCounitTensorNormalization.reassociation
      A N
      hN hA
      (Etale.projectiveLineTraceTransport N hN A hA) Y hY d K =
    AffineOrderedIntegration.ordinarySourceIsoFixed A N hA
      (Etale.projectiveLineTraceTransport N hN A hA) Y hY K d ≪≫
      Etale.ordinaryFiniteTensorRightMapIso A (affineTraceTower Y d)
        (Iso.refl _) ((WeilConjectures.PurityFiniteSetting.DiagonalAffineTrace.coefficientIso
          A N hN hA Y hY d).symm ≪≫
          Etale.CoordinateCounitArrows.towerTateIso A N
            hN hA
            (Etale.projectiveLineTraceTransport N hN A hA) Y hY d) := by
  unfold Etale.OrdinaryAffineCounitTensorNormalization.reassociation
  rw [AffineOrderedIntegration.normalized_source_descent]
  unfold AffineOrderedIntegration.ordinarySourceIsoFixed
    WeilConjectures.PurityFiniteSetting.DiagonalAffineTrace.coefficientIso
  simp only [Iso.trans_assoc]
  congr 2
  unfold Etale.ordinaryFiniteTensorRightMapIso
  simpa only [Functor.mapIso_refl, Iso.refl_trans, Iso.trans_refl,
    Functor.mapIso_trans, NatIso.trans_app, AffineOrderedIntegration.natIso_refl_app,
    Iso.trans_symm,
    Iso.symm_symm_eq, Iso.trans_assoc, Etale.derivedTensorRight,
    Etale.derivedTensorRightFunctor, Etale.ordinaryFinitePullback] using
    AffineOrderedIntegration.bifunctor_iso_transport
      (Etale.derivedTensorRightFunctor
        (ModuleCat.{u + 1} A) (affineTraceTower Y d))
      ((Etale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} A)
        (affineTraceProjection Y d)).app K)
      (Etale.vectorIntegrationBaseCoefficientPullback A
        N hA (Etale.projectiveLineTraceTransport N hN A hA) (affineTraceProjection Y d)
        hY d)
      ((Etale.affineLinearCoefficientDescent A
        N hA (Etale.projectiveLineTraceTransport N hN A hA) Y hY d).symm ≪≫
        Etale.CoordinateCounitArrows.towerTateIso A N
          hN hA
          (Etale.projectiveLineTraceTransport N hN A hA) Y hY d)


private theorem general_normalized_trace (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (Y : Scheme.{u}) [IsNoetherian Y] (hY : IsUnit (N : Γ(Y, ⊤))) (m : ℕ) :
    Etale.OrdinaryAffineCounitTensorNormalization.trace A N hN hA
        (Etale.projectiveLineTraceTransport N hN A hA)
        (fun T _ hT ↦ Etale.projectiveLineTraceDatum N hN A hA T hT) Y hY m =
      (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineProjection Y m)).map
        ((WeilConjectures.PurityFiniteSetting.DiagonalAffineTrace.coefficientIso
          A N hN hA Y hY m).symm ≪≫
            Etale.CoordinateCounitArrows.towerTateIso A N hN hA
              (Etale.projectiveLineTraceTransport N hN A hA) Y hY m).inv ≫
        WeilConjectures.PurityFiniteSetting.DiagonalAffineTrace.ordinaryTrace
          A N hN hA Y hY m := by
  unfold Etale.OrdinaryAffineCounitTensorNormalization.trace
    WeilConjectures.PurityFiniteSetting.DiagonalAffineTrace.ordinaryTrace
    WeilConjectures.PurityFiniteSetting.DiagonalAffineTrace.ordinarySourceIso
  rw [AffineOrderedIntegration.linearComparison_eq]
  simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv,
    Category.assoc] using AffineOrderedIntegration.trace_transport
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineProjection Y m))
    (WeilConjectures.PurityFiniteSetting.DiagonalAffineTrace.coefficientIso
      A N hN hA Y hY m)
    (Etale.CoordinateCounitArrows.towerTateIso A N hN hA
      (Etale.projectiveLineTraceTransport N hN A hA) Y hY m)
    ((Etale.affineDualizingTowerComparison A Y m).inv.app _ ≫
      Etale.affineTraceCounit A N hA (Etale.projectiveLineTraceTransport N hN A hA)
        (fun T _ hT ↦ Etale.projectiveLineTraceDatum N hN A hA T hT) Y hY m)

/-- The ordered counit is tensor integration in the exact ordinary source coordinates.
Source: the ordered affine integration paragraph of the projection-purity agreement
proof (blueprint: lem-pur-general-ordered-counit-normalization).
Proof: apply ordinaryAffineCounit_tensor_normalization. Compare its Tate coefficient
and source reassociation with the fixed ordered coefficient via their canonical
isomorphisms. Projection naturality moves the coefficient comparison through compact
supports; its inverse cancels. The normalized trace then becomes ordinaryTrace. -/
theorem general_ordinary_counit_formula
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (Y : Scheme.{u}) [IsNoetherian Y] (hY : IsUnit (N : Γ(Y, ⊤)))
    (H : Ordinary A Y) (m : ℕ) :
    Etale.compactSupportProjectionMap A (affineProjection Y m)
        (Etale.FiniteSmoothPurity.line A N hA (affineSpace Y m) m) H ≫
      (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineProjection Y m)).map
        (AffineOrderedIntegration.ordinarySourceIsoFixed A N hA
          (Etale.projectiveLineTraceTransport N hN A hA) Y hY H m).inv ≫
      (Etale.affineDualizingTowerComparison A Y m).inv.app _ ≫
      (Etale.affineTraceAdjunction A N hA (Etale.projectiveLineTraceTransport N hN A hA)
        (fun T _ hT ↦ Etale.projectiveLineTraceDatum N hN A hA T hT) Y hY m).counit.app H =
    ((Etale.ordinaryFiniteTensor A Y).obj H).map
      (WeilConjectures.PurityFiniteSetting.DiagonalAffineTrace.ordinaryTrace
        A N hN hA Y hY m) ≫ (Etale.derivedTensorSingleUnitIso H).hom := by
  let t := Etale.projectiveLineTraceTransport N hN A hA
  let D := fun (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))) ↦
    Etale.projectiveLineTraceDatum N hN A hA T hT
  let F := Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineProjection Y m)
  let TC := (Etale.ordinaryFiniteTensor A (affineSpace Y m)).obj
    ((Etale.upperStar (ModuleCat.{u + 1} A) (affineProjection Y m)).mapDerivedCategory.obj H)
  let TD := (Etale.ordinaryFiniteTensor A Y).obj H
  let c := (WeilConjectures.PurityFiniteSetting.DiagonalAffineTrace.coefficientIso
    A N hN hA Y hY m).symm ≪≫
      Etale.CoordinateCounitArrows.towerTateIso A N hN hA t Y hY m
  let eW := AffineOrderedIntegration.ordinarySourceIsoFixed A N hA t Y hY H m
  let eV := Etale.OrdinaryAffineCounitTensorNormalization.reassociation
    A N hN hA t Y hY m H
  let z := (Etale.affineDualizingTowerComparison A Y m).inv.app _ ≫
    (Etale.affineTraceAdjunction A N hA t D Y hY m).counit.app H
  have he : eV = eW ≪≫ TC.mapIso c := by
    simpa only [AffineOrderedIntegration.tensorRightMapIso_refl] using
      general_reassociation_eq A N hN hA Y hY H m
  obtain ⟨q, hq, hn⟩ := Etale.ordinaryAffineCounit_tensor_normalization
    N hN A hA t D Y hY m H
  have hn' : Etale.compactSupportProjectionMap A (affineProjection Y m) _ H ≫
      F.map eV.inv ≫ z = TD.map
        (Etale.OrdinaryAffineCounitTensorNormalization.trace A N hN hA t D Y hY m) ≫
          (Etale.derivedTensorSingleUnitIso H).hom := by
    exact AffineOrderedIntegration.projection_forward q hq rfl hn
  exact AffineOrderedIntegration.normalization_transport F TC TD
    (fun M ↦ Etale.compactSupportProjectionMap A (affineProjection Y m) M H)
    (fun f ↦ AffineOrderedIntegration.projection_naturality A (affineProjection Y m) f H)
    c eW eV he z _ _ (general_normalized_trace A N hN hA Y hY m)
    (Etale.derivedTensorSingleUnitIso H).hom hn'


end AlgebraicGeometry.ProEtale.AffineOrderedIntegrationGeneral
