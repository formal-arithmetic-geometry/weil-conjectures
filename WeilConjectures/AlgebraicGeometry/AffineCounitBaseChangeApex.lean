/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.OrdinaryCoefficientDualizingExchange
public import WeilConjectures.AlgebraicGeometry.CoordinateCounitArrows
import WeilConjectures.AlgebraicGeometry.OrdinaryCoefficientCartesianApexFormula
import WeilConjectures.AlgebraicGeometry.StandardAffineCounitTowerBaseChange
import WeilConjectures.AlgebraicGeometry.VectorIntegrationRestrictedChartCoefficientCore
import WeilConjectures.AlgebraicGeometry.AffineCounitMateUnitChange
import WeilConjectures.AlgebraicGeometry.StandardAffineCounitCoordinateSquare
import WeilConjectures.AlgebraicGeometry.VectorIntegrationBaseCoefficientComposition
import WeilConjectures.AlgebraicGeometry.OrderedTatePullbackSquare
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit

/-! # Affine counit base change with an isomorphic Cartesian apex

Source: orientation-charts proof Step 4, equation (A).
Normalize the tower-counit base-change equation with its coefficient formula,
the ordered Tate square and unit conversion. The coordinate square identifies the
specified map; Cartesian-apex pasting and coefficient composition give the result.
(blueprint: new-lem-pur-affine-counit-base-change-apex).
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
private theorem normalized_affine (P : PurityFiniteSetting.{u})
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    (D : ∀ (Y : Scheme.{u}) [IsNoetherian Y]
      (hY : IsUnit (P.diagonalExponent : Γ(Y, ⊤))),
      Etale.OrdinaryFiniteP1Datum P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t Y hY)
    {S T : Scheme.{u}} [IsNoetherian S] [IsNoetherian T]
    (i : T ⟶ S) (hS : IsUnit (P.diagonalExponent : Γ(S, ⊤))) (d : ℕ) :
    letI := affineTraceNoetherian S d
    letI := affineTraceNoetherian T d
    (Etale.ordinaryFinitePullback P.Coefficient (affineTraceMap i d)).map
      (P.diagonalAffineMate t D S hS d) ≫
      P.ordinaryCoefficientDualizingExchange (affineTraceMap_isPullback i d) =
    (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient
      P.diagonalExponent P.diagonalExponent_annihilates t (affineTraceMap i d)
      (affineTraceInvertible P.diagonalExponent S hS d) d).hom ≫
      P.diagonalAffineMate t D T
        (affineTracePullbackInvertible P.diagonalExponent i hS) d := by
  letI := affineTraceNoetherian S d
  letI := affineTraceNoetherian T d
  let hT := affineTracePullbackInvertible P.diagonalExponent i hS
  have ht := Etale.standardAffineCounit_towerBaseChange P.diagonalExponent
    (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
    P.diagonalExponent_annihilates t D i hS d
  have hx := congrArg Iso.hom (Etale.affineTraceRightBaseChange_unit_coefficient
    P.Coefficient P.diagonalExponent P.diagonalExponent_annihilates t i hS hT d)
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Iso.app_hom] at hx
  have hs := Etale.orderedTatePullbackSquare P.Coefficient P.diagonalExponent
    P.diagonalExponent_annihilates t (affineTraceProjection S d)
    (affineTraceProjection T d) (affineTraceMap i d) i
    (affineTraceMap_isPullback i d).w.symm hS
    (affineTraceInvertible P.diagonalExponent S hS d) hT d
  have hmS := P.affineCounitMate_unitChange t D S hS d
  have hmT := P.affineCounitMate_unitChange t D T hT d
  simp only [unit_inv, Category.comp_id, Iso.trans_inv] at hmS hmT
  simp only [ordinaryCoefficientDualizingExchange, unit_inv, unit_hom,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  erw [hmS]
  simp only [Functor.map_comp, Category.assoc]
  erw [ht]
  rw [reassoc_of% hx]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.id_comp]
  simp only [Etale.derivedSquareUpperStarIso, Iso.trans_inv,
    NatTrans.comp_app, Category.assoc]
  erw [reassoc_of% hs]
  erw [hmT]
  simp only [Category.assoc]

/-- Equation (A) for the affine counit, independently of any vector bundle.
Source: orientation-charts Step 4 and standard affine counit base change.

Proof in words: apply standardAffineCounit_towerBaseChange to i. Its affine
coefficient base-change formula is affineTraceRightBaseChange_unit_coefficient.
The coordinate square identifies b with affineTraceMap i d. The ordered
coefficient regrouping respects pullback: at zero it is unit
composition, and its successor follows by tensoring with the shifted root line.
Use affineCounitMate_unitChange to express the equation at the degree-zero
coefficient unit. Pull back along e and use dualizing_cartesian_apex_isomorphism
for qv, with the fixed apex mate J_e. Coefficient composition gives C_v=e*(C_b) C_e;
reassociate and cancel C_e to obtain v*(M_S) B_v=C_v C_e^{-1} e*(M_T) J_e.
No vector integration, source locality, or nonempty/positive-rank assumption occurs.
(blueprint: new-lem-pur-affine-counit-base-change-apex). -/
theorem affineCounit_baseChange_apex (P : PurityFiniteSetting.{u})
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    (D : ∀ (Y : Scheme.{u}) [IsNoetherian Y]
      (hY : IsUnit (P.diagonalExponent : Γ(Y, ⊤))),
      Etale.OrdinaryFiniteP1Datum P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t Y hY)
    (S T Z : Scheme.{u}) [IsNoetherian S] [IsNoetherian T] [IsNoetherian Z]
    (i : T ⟶ S) (hS : IsUnit (P.diagonalExponent : Γ(S, ⊤))) (d : ℕ)
    (e : Z ≅ affineTraceTower T d) :
    letI := affineTraceNoetherian S d
    letI := affineTraceNoetherian T d
    let hT := affineTracePullbackInvertible P.diagonalExponent i hS
    let b := (affineTraceAffineSpaceIso T d).hom ≫
      AffineSpace.map (ULift.{u} (Fin d)) i ≫ (affineTraceAffineSpaceIso S d).inv
    let v := e.hom ≫ b
    let r := e.hom ≫ affineTraceProjection T d
    letI : HasCompactification r := inferInstance
    ∀ (qv : IsPullback v r (affineTraceProjection S d) i),
      (Etale.ordinaryFinitePullback P.Coefficient v).map
        (P.diagonalAffineMate t D S hS d) ≫
        P.ordinaryCoefficientDualizingExchange qv =
      (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient
        P.diagonalExponent P.diagonalExponent_annihilates t v
        (affineTraceInvertible P.diagonalExponent S hS d) d).hom ≫
      (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient
        P.diagonalExponent P.diagonalExponent_annihilates t e.hom
        (affineTraceInvertible P.diagonalExponent T hT d) d).inv ≫
      (Etale.ordinaryFinitePullback P.Coefficient e.hom).map
        (P.diagonalAffineMate t D T hT d) ≫
      P.ordinaryCoefficientApexComparison e (affineTraceProjection T d) := by
  letI := affineTraceNoetherian S d
  letI := affineTraceNoetherian T d
  intro hT b v r
  letI : HasCompactification r := inferInstance
  intro qv
  have hb : b = affineTraceMap i d := by
    apply (cancel_mono (affineTraceAffineSpaceIso S d).hom).mp
    simpa only [b, Category.assoc, Iso.inv_hom_id, Category.comp_id] using
      (Etale.standardAffineCounit_coordinateSquare i d).symm
  have hv : v = e.hom ≫ affineTraceMap i d := by rw [← hb]
  let qc := affineTraceMap_isPullback i d
  let q : ChosenCartesianSquare (affineTraceMap i d) (affineTraceProjection T d)
      (affineTraceProjection S d) i :=
    { toCommSq := qc.toCommSq
      isoPullback := qc.isoPullback
      hom_fst := qc.isoPullback_hom_fst
      hom_snd := qc.isoPullback_hom_snd }
  have hB := P.ordinaryCoefficientDualizingExchange_apex q e v hv qv
  have hn := (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
    e.hom (affineTraceMap i d) v hv).hom.naturality (P.diagonalAffineMate t D S hS d)
  dsimp only [Functor.comp_map] at hn
  have hC := Etale.vectorIntegrationBaseCoefficientPullback_comp P.Coefficient
    P.diagonalExponent P.diagonalExponent_annihilates t e.hom (affineTraceMap i d) v hv
    (affineTraceInvertible P.diagonalExponent S hS d)
    (affineTraceInvertible P.diagonalExponent T hT d) d
  let Cv := Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient
    P.diagonalExponent P.diagonalExponent_annihilates t v
    (affineTraceInvertible P.diagonalExponent S hS d) d
  let Ce := Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient
    P.diagonalExponent P.diagonalExponent_annihilates t e.hom
    (affineTraceInvertible P.diagonalExponent T hT d) d
  have hC' :
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
        e.hom (affineTraceMap i d) v hv).hom.app _ ≫
        (Etale.ordinaryFinitePullback P.Coefficient e.hom).map
          (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient
            P.diagonalExponent P.diagonalExponent_annihilates t (affineTraceMap i d)
            (affineTraceInvertible P.diagonalExponent S hS d) d).hom =
      Cv.hom ≫ Ce.inv := by
    apply (cancel_mono Ce.hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hC
  have hchart := normalized_affine P t D i hS d
  rw [hB]
  erw [reassoc_of% hn]
  erw [← Functor.map_comp_assoc]
  erw [hchart]
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% hC']
  simp only [Cv, Ce, Etale.ordinaryFinitePullback]

end WeilConjectures.PurityFiniteSetting
