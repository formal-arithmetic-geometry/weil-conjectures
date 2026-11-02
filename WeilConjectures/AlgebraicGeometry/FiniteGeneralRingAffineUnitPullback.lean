/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteGeneralRingAffineLineStep
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Data
import WeilConjectures.AlgebraicGeometry.Finite.General.FiniteGeneralRingLocalTraceAffineLine
import all WeilConjectures.AlgebraicGeometry.Ordered.OrderedTateCoefficientComposition
import WeilConjectures.AlgebraicGeometry.FiniteGeneralRingAffineSuccessorTransition
import WeilConjectures.SmoothPurity.OrdinaryFiniteTwistTransportUniqueness
import WeilConjectures.SmoothPurity.FiniteEtaleTateLinePullback

/-! # Unit trace comparison after inverse image to an affine tower stage
Source: general-ring smooth purity, proof (3), normalized Kummer exponent comparison.
(blueprint: lem-sp-general-ring-affine-unit-pullback).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale
open Etale
attribute [local implicit_reducible] affineTraceTower ordinaryFiniteSingleFunctor
  ordinaryFiniteDegreeZero
set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2


private theorem kummer_pullback
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (M N : ℕ) (hMpos : 0 < M) (hNpos : 0 < N)
    (hM : (M : A) = 0) (hN : (N : A) = 0)
    {S X : Scheme.{u}} (f : X ⟶ S)
    (hS : IsUnit (M : Γ(S, ⊤))) (hS' : IsUnit (N : Γ(S, ⊤)))
    (_hX : IsUnit (M : Γ(X, ⊤))) (_hX' : IsUnit (N : Γ(X, ⊤)))
    (q : S.rootsOfUnitySheaf M ⟶ S.rootsOfUnitySheaf N)
    (b : Scheme.finiteEtaleTateLine S M A hM ≅
      Scheme.finiteEtaleTateLine S N A hN)
    (hb : FiniteGeneralRingKummerComparison A M N hM hN S q b)
    (tN : Etale.OrdinaryFiniteTwistTransport A N hN)
    (tM : Etale.OrdinaryFiniteTwistTransport A M hM) :
    ∃ qX : X.rootsOfUnitySheaf M ⟶ X.rootsOfUnitySheaf N,
      ∃ bX : Scheme.finiteEtaleTateLine X M A hM ≅
        Scheme.finiteEtaleTateLine X N A hN,
      qX = (tM.roots f hS).inv ≫
          (Etale.upperStar AddCommGrpCat.{u + 1} f).map q ≫
          (tN.roots f hS').hom ∧
      bX = (tM.line f hS).symm ≪≫
          (Etale.upperStar (ModuleCat.{u + 1} A) f).mapIso b ≪≫
          (tN.line f hS') ∧
      FiniteGeneralRingKummerComparison A M N hM hN X qX bX := by
  have _ := hMpos
  have _ := hNpos
  let qX := (tM.roots f hS).inv ≫
    (Etale.upperStar AddCommGrpCat.{u + 1} f).map q ≫ (tN.roots f hS').hom
  let bX := (tM.line f hS).symm ≪≫
    (Etale.upperStar (ModuleCat.{u + 1} A) f).mapIso b ≪≫ (tN.line f hS')
  refine ⟨qX, bX, rfl, rfl, ?_⟩
  have hrootsN : (tN.roots f hS').hom =
      upperStarRootsOfUnitySheafToRootsOfUnitySheaf N f := by
    apply (cancel_mono (kernel.ι (N • 𝟙 X.gmSheaf))).mp
    rw [← tN.roots_normalization,
      upperStarRootsOfUnitySheafToRootsOfUnitySheaf_ι]
  constructor
  · dsimp [qX]
    rw [hrootsN]
    simp only [Category.assoc, upperStarRootsOfUnitySheafToRootsOfUnitySheaf_ι]
    erw [← Functor.map_comp_assoc, hb.1]
    simp only [Functor.map_nsmul]
    rw [Preadditive.nsmul_comp, Preadditive.comp_nsmul]
    change (M / N) • ((tM.roots f hS).inv ≫
      (Etale.upperStar AddCommGrpCat.{u + 1} f).map (S.rootsOfUnitySheafι M) ≫
      upperStarGmSheafToGmSheaf f) = _
    have hm' :
        (Etale.upperStar AddCommGrpCat.{u + 1} f).map (S.rootsOfUnitySheafι M) ≫
          upperStarGmSheafToGmSheaf f =
        (tM.roots f hS).hom ≫ kernel.ι (M • 𝟙 X.gmSheaf) := by
      exact tM.roots_normalization f hS
    change (M / N) • ((tM.roots f hS).inv ≫
      ((Etale.upperStar AddCommGrpCat.{u + 1} f).map (S.rootsOfUnitySheafι M) ≫
        upperStarGmSheafToGmSheaf f)) = _
    rw [hm']
    simp only [Iso.inv_hom_id_assoc]
  · have hgen : lineHomEquiv X M A hM _ bX.hom =
        qX ≫ lineHomEquiv X N A hN _ (𝟙 _) := by
      apply (cancel_epi (tM.roots f hS).hom).mp
      apply ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv
        _ _).injective
      rw [← Etale.normalized_line_transpose A M hM tM f hS]
      have he : (tM.line f hS).hom ≫ bX.hom =
          (Etale.upperStar (ModuleCat.{u + 1} A) f).map b.hom ≫
            (tN.line f hS').hom := by
        simp [bX]
      rw [he, Adjunction.homEquiv_naturality_left]
      have hq : (tM.roots f hS).hom ≫ qX =
          (Etale.upperStar AddCommGrpCat.{u + 1} f).map q ≫
            (tN.roots f hS').hom := by
        simp [qX]
      rw [← Category.assoc, hq, Category.assoc,
        Adjunction.homEquiv_naturality_left]
      rw [← Etale.normalized_line_transpose A N hN tN f hS']
      simp only [Category.comp_id]
      ext W z
      simp only [lineHomEquiv_generator]
      change (((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).homEquiv
        _ _ (tN.line f hS').hom).hom.app W)
          (b.hom.hom.app W
            (finiteEtaleTateOneGenerator A M S hM W 1 z)) = _
      rw [hb.2]
      rfl
    intro W a z
    have hz := congrArg (fun g ↦ g.hom.app W z) hgen
    simp only [lineHomEquiv_generator] at hz
    change bX.hom.hom.app W (finiteEtaleTateOneGenerator A M X hM W a z) = _
    rw [finiteEtaleGenerator_smul, _root_.map_smul, hz]
    exact (finiteEtaleGenerator_smul X N A hN W a
      (qX.hom.app W z)).symm

private theorem line_id (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hN : 0 < N) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))) :
    t.line (𝟙 T) hT = (Etale.upperStarId (ModuleCat.{u + 1} A) T).app
      (Scheme.finiteEtaleTateLine T N A hA) := by
  obtain ⟨l, hl, hid, _⟩ :=
    Scheme.finiteEtaleTateLine_pullback_normalized A N hN hA
  have hr {U V : Scheme.{u}} (v : U ⟶ V) (hV : IsUnit (N : Γ(V, ⊤))) :
      (t.roots v hV).hom = Scheme.upperStarRootsOfUnitySheafToRootsOfUnitySheaf N v := by
    apply (cancel_mono (kernel.ι (N • 𝟙 U.gmSheaf))).mp
    exact (t.roots_normalization v hV).symm.trans
      (Scheme.upperStarRootsOfUnitySheafToRootsOfUnitySheaf_ι N v).symm
  let t' : OrdinaryFiniteTwistTransport A N hA :=
    { roots := t.roots
      line := fun {X Y} f hY ↦ @l Y X f hY
      roots_normalization := t.roots_normalization
      line_normalization := by
        intro U V v hV W a z
        dsimp only
        rw [hr]
        exact hl v hV W a z }
  have he := ordinaryFiniteTwistTransport_unique A N hA t t'
  exact (congrArg (fun t₀ ↦ t₀.line (𝟙 T) hT) he).trans (hid T hT)

private theorem shifted_line_square
    (A : Type (u + 1)) [CommRing A] (M N : ℕ)
    (hM : (M : A) = 0) (hN : (N : A) = 0)
    (tM : OrdinaryFiniteTwistTransport A M hM)
    (tN : OrdinaryFiniteTwistTransport A N hN)
    {X T : Scheme.{u}} (f : X ⟶ T)
    (hMT : IsUnit (M : Γ(T, ⊤))) (hNT : IsUnit (N : Γ(T, ⊤)))
    (b : Scheme.finiteEtaleTateLine T M A hM ≅
      Scheme.finiteEtaleTateLine T N A hN)
    (c : Scheme.finiteEtaleTateLine X M A hM ≅
      Scheme.finiteEtaleTateLine X N A hN)
    (hc : (Etale.upperStar (ModuleCat.{u + 1} A) f).map b.hom ≫
        (tN.line f hNT).hom = (tM.line f hMT).hom ≫ c.hom) :
    (ordinaryFinitePullback A f).map
        ((shiftFunctor _ (2 : ℤ)).map ((DerivedCategory.singleFunctor _ 0).map b.hom)) ≫
      (ordinaryFiniteShiftedLinePullback A N hN tN f hNT).hom =
    (ordinaryFiniteShiftedLinePullback A M hM tM f hMT).hom ≫
      (shiftFunctor _ (2 : ℤ)).map ((DerivedCategory.singleFunctor _ 0).map c.hom) := by
  let : (ordinaryFinitePullback A f).CommShift ℤ :=
    Etale.commShiftLeftDerivedUpperStar (ModuleCat.{u + 1} A) f
  have hsingle := (ordinaryFiniteSinglePullbackIso A f).hom.naturality b.hom
  have hshift := ((ordinaryFinitePullback A f).commShiftIso (2 : ℤ)).hom.naturality
    ((ordinaryFiniteSingleFunctor A T).map b.hom)
  simp only [Functor.comp_map] at hsingle hshift
  simp only [ordinaryFiniteShiftedLinePullback, shiftedSinglePullbackIsoWith,
    Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  simp only [ordinaryFiniteSingleFunctor_eq, ordinaryFinitePullback] at hsingle hshift ⊢
  rw [reassoc_of% hshift]
  congr 1
  rw [← Functor.map_comp, ← Functor.map_comp, reassoc_of% hsingle]
  simp only [← Functor.map_comp, hc]

private theorem line_step_stage
    (A : Type (u + 1)) [CommRing A] (M N : ℕ)
    (hM : (M : A) = 0) (hN : (N : A) = 0)
    (tM : OrdinaryFiniteTwistTransport A M hM)
    (tN : OrdinaryFiniteTwistTransport A N hN)
    (T : Scheme.{u}) (hMT : IsUnit (M : Γ(T, ⊤))) (hNT : IsUnit (N : Γ(T, ⊤)))
    (b : Scheme.finiteEtaleTateLine T M A hM ≅
      Scheme.finiteEtaleTateLine T N A hN) (d : ℕ)
    (hMpos : 0 < M) (hNpos : 0 < N)
    (c : Scheme.finiteEtaleTateLine (affineTraceTower T d) M A hM ≅
      Scheme.finiteEtaleTateLine (affineTraceTower T d) N A hN)
    (hc : (Etale.upperStar (ModuleCat.{u + 1} A) (affineTraceProjection T d)).map
        b.hom ≫ (tN.line (affineTraceProjection T d) hNT).hom =
      (tM.line (affineTraceProjection T d) hMT).hom ≫ c.hom)
    (K : DerivedCategoryModule A (affineTraceTower T d)) :
    finiteGeneralRingAffineLineStep A M N hM hN tM tN T hMT hNT b d K =
      finiteGeneralRingAffineLineStep A M N hM hN tM tN (affineTraceTower T d)
        (affineTraceInvertible M T hMT d) (affineTraceInvertible N T hNT d) c 0 K := by
  let U := affineTraceTower T d
  let shiftedC := (shiftFunctor (DerivedCategoryModule A U) (2 : ℤ)).map
    ((DerivedCategory.singleFunctor _ 0).map c.hom)
  have hstage : (finiteGeneralRingShiftedStageComparison A M N hM hN tM tN T
      hMT hNT b d).hom = shiftedC := by
    simp only [finiteGeneralRingShiftedStageComparison, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_hom]
    rw [shifted_line_square A M N hM hN tM tN (affineTraceProjection T d)
      hMT hNT b c hc, Iso.inv_hom_id_assoc]
  have hid : (Etale.upperStar (ModuleCat.{u + 1} A) (𝟙 U)).map c.hom ≫
        (tN.line (𝟙 U) (affineTraceInvertible N T hNT d)).hom =
      (tM.line (𝟙 U) (affineTraceInvertible M T hMT d)).hom ≫ c.hom := by
    rw [line_id A N hNpos hN tN U, line_id A M hMpos hM tM U]
    exact (Etale.upperStarId (ModuleCat.{u + 1} A) U).hom.naturality c.hom
  have hzero : (finiteGeneralRingShiftedStageComparison A M N hM hN tM tN U
      (affineTraceInvertible M T hMT d) (affineTraceInvertible N T hNT d) c 0).hom =
      shiftedC := by
    simp only [finiteGeneralRingShiftedStageComparison, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_hom]
    rw [Iso.inv_comp_eq]
    exact shifted_line_square A M N hM hN tM tN (𝟙 U) _ _ c c hid
  dsimp only [U] at hzero
  unfold finiteGeneralRingAffineLineStep
  rw [hstage, hzero]
  rfl

private theorem counit_one
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (Y : Scheme.{u}) [IsNoetherian Y] (hY : IsUnit (N : Γ(Y, ⊤))),
      OrdinaryFiniteP1Datum A N hA t Y hY)
    (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))) :
    affineTraceCounit A N hA t D T hT 1 =
      (affineTraceLineAdjunction A N hA t T hT (D T hT)).counit.app
        (ordinaryFiniteUnit A T) := by
  unfold affineTraceCounit affineTraceAdjunction
  rw [affineTraceAdjunctionTower_counit_succ]
  change _ ≫ 𝟙 _ = _
  simp only [Category.comp_id, affineTraceLeftTower]
  rfl

/-- The line comparison pulled from the original base preserves the normalized
last-coordinate counit on the coefficient unit. No preceding tower transition or
induction hypothesis occurs in this statement.

Source: general-ring smooth purity, proof (3), exponent independence on charts;
Kummer inverse-image normalization, Stacks Tags 03PK and 03Q1.
(blueprint: lem-sp-general-ring-affine-unit-pullback).

Proof: pull q back along the preceding tower projection and conjugate by the two
normalized roots-of-unity pullback isomorphisms. The kernel-inclusion normalization
of these isomorphisms carries the first Kummer-comparison equation to the same
equation on this tower stage. Pull b back and conjugate by the normalized coefficient
line comparisons. Test on each scalar/root generator; line normalization and the
second clause of hb give the generator clause of the pulled-back Kummer comparison.
Apply finiteGeneralRingLocalTraceExponent_affine_line on this base, with the two
specified normalized projective-line data. Identify its level-one transition with
the displayed lineStep: expand the zero coefficient descent, the successor descent,
and the level-one power, then cancel inverse-image identity and tensor-unit
comparisons. Exact single-degree inverse image and shift naturality identify the
shift of the sheaf comparison with finiteGeneralRingShiftedStageComparison. The
normalized unit and open counits identify the level-one counit with the displayed
line adjunction counit. Thus the existing affine-line theorem gives precisely this
square; no new orientation or arbitrary natural transformation is chosen.
-/
theorem finiteGeneralRingAffineUnit_pullback
    (A : Type (u + 1)) [CommRing A] [Finite A] (M N : ℕ)
    (hM : (M : A) = 0) (hN : (N : A) = 0)
    (tM : OrdinaryFiniteTwistTransport A M hM)
    (tN : OrdinaryFiniteTwistTransport A N hN)
    (T : Scheme.{u}) (hMunit : IsUnit (M : Γ(T, ⊤)))
    (hNunit : IsUnit (N : Γ(T, ⊤)))
    (b : Scheme.finiteEtaleTateLine T M A hM ≅
      Scheme.finiteEtaleTateLine T N A hN) (d : ℕ)
    (hMpos : 0 < M) (hNpos : 0 < N)
    (q : T.rootsOfUnitySheaf M ⟶ T.rootsOfUnitySheaf N)
    (hb : FiniteGeneralRingKummerComparison A M N hM hN T q b)
    [IsNoetherian (affineTraceTower T d)]
    (DM : ∀ (Y : Scheme.{u}) [IsNoetherian Y] (hY : IsUnit (M : Γ(Y, ⊤))),
      OrdinaryFiniteP1Datum A M hM tM Y hY)
    (DN : ∀ (Y : Scheme.{u}) [IsNoetherian Y] (hY : IsUnit (N : Γ(Y, ⊤))),
      OrdinaryFiniteP1Datum A N hN tN Y hY) :
    (affineTraceLineLeft A (affineTraceTower T d)).map
        (finiteGeneralRingAffineLineStep A M N hM hN tM tN T hMunit hNunit b d
          (ordinaryFiniteUnit A (affineTraceTower T d))) ≫
      (affineTraceLineAdjunction A N hN tN (affineTraceTower T d)
        (affineTraceInvertible N T hNunit d)
        (DN (affineTraceTower T d) (affineTraceInvertible N T hNunit d))).counit.app
          (ordinaryFiniteUnit A (affineTraceTower T d)) =
    (affineTraceLineAdjunction A M hM tM (affineTraceTower T d)
      (affineTraceInvertible M T hMunit d)
      (DM (affineTraceTower T d) (affineTraceInvertible M T hMunit d))).counit.app
        (ordinaryFiniteUnit A (affineTraceTower T d)) := by
  let U := affineTraceTower T d
  let p : U ⟶ T := affineTraceProjection T d
  let hMU := affineTraceInvertible M T hMunit d
  let hNU := affineTraceInvertible N T hNunit d
  obtain ⟨qU, bU, _, hbUcomp, hbU⟩ := kummer_pullback A M N hMpos hNpos hM hN p
    hMunit hNunit hMU hNU q b hb tN tM
  have hc : (Etale.upperStar (ModuleCat.{u + 1} A) p).map b.hom ≫
      (tN.line p hNunit).hom = (tM.line p hMunit).hom ≫ bU.hom := by
    rw [hbUcomp]
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      Iso.hom_inv_id_assoc]
  let e := (affineLinearCoefficientDescent A M hM tM U hMU 1).hom ≫
    (ordinaryFinitePullback A (affineTraceProjection U 1)).map
      (finiteGeneralRingLevelPower A M N hM hN U bU 1).hom ≫
    (affineLinearCoefficientDescent A N hN tN U hNU 1).inv
  have hz : 𝟙 (ordinaryFiniteUnit A U) =
      (affineLinearCoefficientDescent A M hM tM U hMU 0).hom ≫
        (ordinaryFinitePullback A (affineTraceProjection U 0)).map
          (finiteGeneralRingLevelPower A M N hM hN U bU 0).hom ≫
        (affineLinearCoefficientDescent A N hN tN U hNU 0).inv := by
    simp only [affineLinearCoefficientDescent, finiteGeneralRingLevelPower]
    change 𝟙 _ = ((affineLinearPullbackId A U).app _).inv ≫
      (ordinaryFinitePullback A (𝟙 U)).map (𝟙 _) ≫
      ((affineLinearPullbackId A U).app _).hom
    simp
  have hf := finiteGeneralRingAffineSuccessorTransition A M N hM hN U hMU hNU bU
    tN tM 0 (𝟙 (ordinaryFiniteUnit A U)) hz e rfl
  have he : e = finiteGeneralRingAffineLineStep A M N hM hN tM tN U hMU hNU bU 0
      (ordinaryFiniteUnit A U) := by
    change e = finiteGeneralRingAffineLineStep A M N hM hN tM tN U hMU hNU bU 0
      (ordinaryFiniteUnit A U) ≫ (affineTraceLineRight A N hN U).map
        (𝟙 (ordinaryFiniteUnit A U)) at hf
    have hi := (affineTraceLineRight A N hN U).map_id (ordinaryFiniteUnit A U)
    rw [hi] at hf
    exact hf.trans (Category.comp_id _)
  have hline := finiteGeneralRingLocalTraceExponent_affine_line A M N hMpos hNpos
    hM hN U hMU hNU qU bU hbU tN DN tM DM e rfl
  rw [he, counit_one, counit_one] at hline
  rw [line_step_stage A M N hM hN tM tN T hMunit hNunit b d hMpos hNpos bU hc]
  exact hline

end AlgebraicGeometry.ProEtale
