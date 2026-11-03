/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FrobeniusExchange.SystemOperationExchangeRealization
import WeilConjectures.SixFunctors.FrobeniusExchange.SystemCompactExchangeEvaluation

/-! # Finite coordinates for the compact Frobenius exchange

Source: the proper/open compact-support transport and coefficient compatibility in
Steps 2 and 5 of the blueprint proof of Weil equivariance of purity and trace;
projection normalization of the simultaneous system realization.
(blueprint: lem-pur-frobenius-compact-finite-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Functor
namespace WeilConjectures.FrobeniusExchange
/-- A finite exchange written in prescribed pullback and compact-support coordinates.
Source: categorical composition of the three comparisons in blueprint Step 2
(blueprint: lem-pur-frobenius-compact-finite-coordinates). -/
@[irreducible] def finiteCoordinateWord
    {FX FY : Type*} [Category FX] [Category FY]
    (F : FX ⥤ FY) {PX : FX ⥤ FX} (PY : FY ⥤ FY)
    (ef : F ⋙ PY ⟶ PX ⋙ F) {K Q : FX} {U V : FY}
    (kX : Q ≅ PX.obj K) (kY : U ≅ PY.obj V) (sK : V ⟶ F.obj K) :
    U ⟶ F.obj Q :=
  kY.hom ≫ PY.map sK ≫ ef.app K ≫ F.map kX.inv

private theorem finiteCoordinateTransport
    {IX IY SX SY FX FY : Type*}
    [Category IX] [Category IY] [Category SX] [Category SY] [Category FX] [Category FY]
    (RX : IX ⥤ SX) (RY : IY ⥤ SY) (EX : SX ⥤ FX) (EY : SY ⥤ FY)
    (DX : IX ⥤ FX) (DY : IY ⥤ FY) (H : SX ⥤ SY) (F : FX ⥤ FY)
    (GX : SX ⥤ SX) (GY : SY ⥤ SY) (PX : FX ⥤ FX) (PY : FY ⥤ FY)
    (rX : RX ⋙ EX ≅ DX) (rY : RY ⋙ EY ≅ DY)
    (d : H ⋙ EY ≅ EX ⋙ F) (qX : GX ⋙ EX ≅ EX ⋙ PX) (qY : GY ⋙ EY ≅ EY ⋙ PY)
    (ef : F ⋙ PY ⟶ PX ⋙ F) (K Q : IX) (U V W : IY) (a : U ⟶ W)
    (bX : RX.obj Q ≅ GX.obj (RX.obj K)) (bY : RY.obj U ≅ GY.obj (RY.obj V))
    (oK : RY.obj V ⟶ H.obj (RX.obj K)) (oQ : RY.obj W ⟶ H.obj (RX.obj Q))
    (e : GY.obj (H.obj (RX.obj K)) ⟶ H.obj (GX.obj (RX.obj K)))
    (kX : DX.obj Q ≅ PX.obj (DX.obj K)) (kY : DY.obj U ≅ PY.obj (DY.obj V))
    (sK : DY.obj V ⟶ F.obj (DX.obj K)) (sQ : DY.obj W ⟶ F.obj (DX.obj Q))
    (hr : RY.map a ≫ oQ ≫ H.map bX.hom = bY.hom ≫ GY.map oK ≫ e)
    (he : EY.map e ≫ d.hom.app (GX.obj (RX.obj K)) ≫ F.map (qX.hom.app (RX.obj K)) =
      qY.hom.app (H.obj (RX.obj K)) ≫ PY.map (d.hom.app (RX.obj K)) ≫ ef.app (EX.obj (RX.obj K)))
    (hsK : sK = rY.inv.app V ≫ EY.map oK ≫ d.hom.app (RX.obj K) ≫
      F.map (rX.hom.app K))
    (hsQ : sQ = rY.inv.app W ≫ EY.map oQ ≫ d.hom.app (RX.obj Q) ≫
      F.map (rX.hom.app Q))
    (hkX : kX.hom = rX.inv.app Q ≫ EX.map bX.hom ≫ qX.hom.app (RX.obj K) ≫
      PX.map (rX.hom.app K))
    (hkY : kY.hom = rY.inv.app U ≫ EY.map bY.hom ≫ qY.hom.app (RY.obj V) ≫
      PY.map (rY.hom.app V)) :
    DY.map a ≫ sQ = finiteCoordinateWord F PY ef kX kY sK := by
  unfold finiteCoordinateWord
  apply (cancel_mono (F.map kX.hom)).1
  simp only [Category.assoc, ← F.map_comp, Iso.inv_hom_id]
  simp only [F.map_id]
  rw [hsQ, hkX, hkY, hsK]
  simp only [Functor.map_comp, Category.assoc]
  rw [← F.map_comp_assoc (rX.hom.app Q) (rX.inv.app Q),
    rX.hom_inv_id_app, F.map_id, Category.id_comp]
  rw [← PY.map_comp_assoc (rY.hom.app V) (rY.inv.app V),
    rY.hom_inv_id_app, PY.map_id, Category.id_comp]
  have hd := d.hom.naturality bX.hom
  dsimp only [Functor.comp_map] at hd
  rw [← reassoc_of% hd]
  have ha := rY.inv.naturality a
  dsimp only [Functor.comp_map] at ha
  rw [reassoc_of% ha]
  rw [← EY.map_comp_assoc, ← EY.map_comp_assoc, Category.assoc, hr]
  simp only [EY.map_comp, Category.assoc]
  rw [reassoc_of% he]
  have hq := qY.hom.naturality oK
  dsimp only [Functor.comp_map] at hq
  rw [reassoc_of% hq]
  have hf := ef.naturality (rX.hom.app K)
  dsimp only [Functor.comp_map] at hf
  rw [reassoc_of% hf]
  simp only [Category.comp_id]

private theorem evaluation_change_coordinates
    {SX SY FX FY : Type*} [Category SX] [Category SY] [Category FX] [Category FY]
    (EX : SX ⥤ FX) (EY : SY ⥤ FY) (H : SX ⥤ SY) (F : FX ⥤ FY)
    (GX : SX ⥤ SX) (GY : SY ⥤ SY) (UX PX : FX ⥤ FX) (UY PY : FY ⥤ FY)
    (d₀ d₁ : H ⋙ EY ≅ EX ⋙ F)
    (x : GX ⋙ EX ≅ EX ⋙ UX) (y : GY ⋙ EY ≅ EY ⋙ UY)
    (tx : UX ≅ PX) (ty : UY ≅ PY)
    (qX : GX ⋙ EX ≅ EX ⋙ PX) (qY : GY ⋙ EY ≅ EY ⋙ PY)
    (N : SX) (e : GY.obj (H.obj N) ⟶ H.obj (GX.obj N))
    (ef : PY.obj (F.obj (EX.obj N)) ⟶ F.obj (PX.obj (EX.obj N)))
    (hd : d₀ = d₁) (hx : qX = x ≪≫ isoWhiskerLeft EX tx)
    (hy : qY = y ≪≫ isoWhiskerLeft EY ty)
    (h : EY.map e ≫
          (d₁.app (GX.obj N) ≪≫ F.mapIso (x.app N ≪≫ tx.app (EX.obj N))).hom =
        (y.app (H.obj N) ≪≫ UY.mapIso (d₁.app N) ≪≫
          ty.app (F.obj (EX.obj N))).hom ≫ ef) :
    EY.map e ≫ d₀.hom.app (GX.obj N) ≫ F.map (qX.hom.app N) =
      qY.hom.app (H.obj N) ≫ PY.map (d₀.hom.app N) ≫ ef := by
  subst d₀
  subst qX
  subst qY
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp,
    NatTrans.comp_app, isoWhiskerLeft_hom, whiskerLeft_app, Category.assoc] at h ⊢
  have hn := ty.hom.naturality (d₁.hom.app N)
  rw [reassoc_of% hn] at h
  exact h

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Evaluation of system pullback in finite tensor coordinates.
Source: the normalized quotient evaluation and tensor pullback comparisons of
`def-weil-system-operation-exchange-realization`.
(blueprint: lem-pur-frobenius-compact-finite-coordinates). -/
def finitePullEvaluation {X : Scheme.{u}} (g : X ⟶ X) (n : ℕ) :
    integralComparisonDerivedSequencePullback l E g ⋙
        coefficientSequenceDerivedEvaluation l E X n ≅
      coefficientSequenceDerivedEvaluation l E X n ⋙
        proEtaleConstantRingDerivedPullback
          (Padic.coefficientExtensionRing l E (n + 1)) g :=
  (systemPullEvaluation l E g n).symm ≪≫
    isoWhiskerLeft (coefficientSequenceDerivedEvaluation l E X n)
      (openSquareDerivedPullbackModel
        (Padic.coefficientExtensionRing l E (n + 1)) g).symm

/-- Pullback followed by reduction, in the normalized finite tensor coordinates.
Source: the effective pullback counit and reduction evaluation of the simultaneous
system realization (blueprint: lem-pur-frobenius-compact-finite-coordinates). -/
def finitePullCoordinates {X : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    (g : X ⟶ X) (K : sfIntegralConstructibleCategory l E X) (n : ℕ) :
    (scalarReductionDerivedExtension l E X n).obj
        ((constructibleIntegralPullback l E g).obj K).obj ≅
      (proEtaleConstantRingDerivedPullback
        (Padic.coefficientExtensionRing l E (n + 1)) g).obj
          ((scalarReductionDerivedExtension l E X n).obj K.obj) :=
  (((models l E).system X).reductionEvaluation n).symm.app
      ((constructibleIntegralPullback l E g).obj K).obj ≪≫
    (coefficientSequenceDerivedEvaluation l E X n).mapIso
      ((reductionPullbackIso l E g).app K) ≪≫
    (finitePullEvaluation l E g n).app ((reduction l E X).obj K.obj) ≪≫
    (proEtaleConstantRingDerivedPullback
      (Padic.coefficientExtensionRing l E (n + 1)) g).mapIso
      ((((models l E).system X).reductionEvaluation n).app K.obj)

-- Keep the chosen models fixed while comparing the light functor wrappers.
attribute [local irreducible] HasDerivedCategory.standard scalarReductionDerivedExistence
  completedIntegralCoefficientSheafUnrestricted models compactRealization
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  scalarReductionExistence unrestrictedIntegralReductionExistence constantSheaf
  coefficientSequenceEvaluation coefficientSequenceTransition Padic.coefficientExtensionIdeal
attribute [local implicit_reducible] compactImage realize constructibleIntegralPullback
  sfIntrinsicCompactSupport sfAmbientCompactSupportCandidate
attribute [local irreducible] compactIntegral compactIntegralAmbient reductionPullbackIso
  systemCompactExchange finiteCompact

private def finiteReductionEvaluation {X : Scheme.{u}} (n : ℕ) :
    reduction l E X ⋙ coefficientSequenceDerivedEvaluation l E X n ≅
      scalarReductionDerivedExtension l E X n :=
  ((models l E).system X).reductionEvaluation n

private def finiteSupportFunctor {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (n : ℕ) :
    normalizedDVRDerived l E X n ⥤ normalizedDVRDerived l E Y n :=
  letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))

private def finitePullFunctor {X : Scheme.{u}} (g : X ⟶ X) (n : ℕ) :
    normalizedDVRDerived l E X n ⥤ normalizedDVRDerived l E X n :=
  proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E (n + 1)) g

private theorem finitePullCoordinates_hom {X : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    (g : X ⟶ X) (K : sfIntegralConstructibleCategory l E X) (n : ℕ) :
    (finitePullCoordinates l E g K n).hom =
      (finiteReductionEvaluation l E (X := X) n).inv.app
          ((constructibleIntegralPullback l E g).obj K).obj ≫
        (coefficientSequenceDerivedEvaluation l E X n).map
          ((reductionPullbackIso l E g).app K).hom ≫
        (finitePullEvaluation l E g n).hom.app ((reduction l E X).obj K.obj) ≫
        (finitePullFunctor l E g n).map
            ((finiteReductionEvaluation l E (X := X) n).hom.app K.obj) := by
  rfl

@[irreducible] private def compactEvaluation
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (n : ℕ) :
    let A := Padic.coefficientExtensionRing l E (n + 1)
    letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
    (systemDerivedOpen l E c.i ⋙ systemDirect l E c.g) ⋙
        coefficientSequenceDerivedEvaluation l E Y n ≅
      coefficientSequenceDerivedEvaluation l E X n ⋙ sfIntrinsicCompactSupport c A := by
  let A := Padic.coefficientExtensionRing l E (n + 1)
  letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  exact isoWhiskerLeft (systemDerivedOpen l E c.i)
      (@asIso _ _ _ _ (systemDirectEvaluation l E c.g n)
        (systemDirectEvaluation_isIso l E c.g n)) ≪≫
    isoWhiskerRight
      (@asIso _ _ _ _ (systemOpenEvaluationInv l E c.i n)
        (systemOpenEvaluationInv_isIso l E c.i n)).symm
      (proEtaleConstantDerivedDirectImage c.g A)

private theorem compactExchange_tensor
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (gX : X ⟶ X) (gB : c.Z ⟶ c.Z) (gY : Y ⟶ Y)
    (wp : gB ≫ c.g = c.g ≫ gY) (sj : IsPullback gX c.i c.i gB)
    (n : ℕ) (N : coefficientSequenceDerived l E X) :
    letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
    let d := compactEvaluation (l := l) (E := E) (f := f) (c := c) n
    (coefficientSequenceDerivedEvaluation l E Y n).map
          ((systemCompactExchange l E c gX gB gY wp sj).app N) ≫
        d.hom.app ((integralComparisonDerivedSequencePullback l E gX).obj N) ≫
        (finiteSupportFunctor l E c n).map ((finitePullEvaluation l E gX n).hom.app N) =
      (finitePullEvaluation l E gY n).hom.app
          ((systemDerivedOpen l E c.i ⋙ systemDirect l E c.g).obj N) ≫
        (finitePullFunctor l E gY n).map (d.hom.app N) ≫
        (finiteCompact l E (n + 1) (Nat.succ_pos n) c gX gB gY wp sj).app
          ((coefficientSequenceDerivedEvaluation l E X n).obj N) := by
  let := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  exact evaluation_change_coordinates
    (coefficientSequenceDerivedEvaluation l E X n)
    (coefficientSequenceDerivedEvaluation l E Y n)
    (systemDerivedOpen l E c.i ⋙ systemDirect l E c.g)
    (finiteSupportFunctor l E c n)
    (integralComparisonDerivedSequencePullback l E gX)
    (integralComparisonDerivedSequencePullback l E gY)
    (sfIntrinsicDerivedPullback (Padic.coefficientExtensionRing l E (n + 1)) gX)
    (finitePullFunctor l E gX n)
    (sfIntrinsicDerivedPullback (Padic.coefficientExtensionRing l E (n + 1)) gY)
    (finitePullFunctor l E gY n)
    (compactEvaluation (l := l) (E := E) (f := f) (c := c) n)
    (isoWhiskerLeft (systemDerivedOpen l E c.i)
        (@asIso _ _ _ _ (systemDirectEvaluation l E c.g n)
          (systemDirectEvaluation_isIso l E c.g n)) ≪≫
      isoWhiskerRight
        (@asIso _ _ _ _ (systemOpenEvaluationInv l E c.i n)
          (systemOpenEvaluationInv_isIso l E c.i n)).symm
        (proEtaleConstantDerivedDirectImage c.g
          (Padic.coefficientExtensionRing l E (n + 1))))
    (systemPullEvaluation l E gX n).symm (systemPullEvaluation l E gY n).symm
    (openSquareDerivedPullbackModel (Padic.coefficientExtensionRing l E (n + 1)) gX).symm
    (openSquareDerivedPullbackModel (Padic.coefficientExtensionRing l E (n + 1)) gY).symm
    (finitePullEvaluation l E gX n) (finitePullEvaluation l E gY n)
    N ((systemCompactExchange l E c gX gB gY wp sj).app N)
    ((finiteCompact l E (n + 1) (Nat.succ_pos n) c gX gB gY wp sj).app
      ((coefficientSequenceDerivedEvaluation l E X n).obj N))
    (by unfold compactEvaluation; rfl) rfl rfl
    (systemCompactExchange_evaluation l E c gX gB gY wp sj n N)

section Compact
variable (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
  [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
  [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of K₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  (c : Compactification f)
  (gX : X ⟶ X) (gB : c.Z ⟶ c.Z) (gY : Y ⟶ Y) [IsIso gX] [IsIso gY]
  (wp : gB ≫ c.g = c.g ≫ gY) (sj : IsPullback gX c.i c.i gB)

/-- The finite proper/open mate with the recorded input and output reduction coordinates.
Source: blueprint compact-support transport, with its fixed proper and open mates.
(blueprint: lem-pur-frobenius-compact-finite-coordinates). -/
def compactFiniteCoordinates (K : sfIntegralConstructibleCategory l E X) (n : ℕ) :
    (scalarReductionDerivedExtension l E Y n).obj
        ((constructibleIntegralPullback l E gY).obj
          ((sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj K)).obj ⟶
      (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))).obj
        ((scalarReductionDerivedExtension l E X n).obj
          ((constructibleIntegralPullback l E gX).obj K).obj) :=
  letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  let P : normalizedDVRDerived l E Y n ⥤ normalizedDVRDerived l E Y n :=
    proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E (n + 1)) gY
  let F : normalizedDVRDerived l E X n ⥤ normalizedDVRDerived l E Y n :=
    sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))
  finiteCoordinateWord F P
    (finiteCompact l E (n + 1) (Nat.succ_pos n) c gX gB gY wp sj)
    (finitePullCoordinates l E gX K n)
    (finitePullCoordinates l E gY
      ((sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj K) n)
    (sfCompactSupportFiniteReductionIso l K₀ hl c E K n).hom

private theorem compactFiniteReduction_coordinates
    (T : sfIntegralConstructibleCategory l E X) (n : ℕ) :
    let A := Padic.coefficientExtensionRing l E (n + 1)
    letI := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
    (sfCompactSupportFiniteReductionIso l K₀ hl c E T n).hom =
      (((models l E).system Y).reductionEvaluation n).inv.app
          ((sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj T).obj ≫
        (coefficientSequenceDerivedEvaluation l E Y n).map
          ((compactOperationReduction l E K₀ hl f c).app T) ≫
        (compactEvaluation (l := l) (E := E) (f := f) (c := c) n).hom.app
          ((reduction l E X).obj T.obj) ≫
        (sfIntrinsicCompactSupport c A).map
          ((((models l E).system X).reductionEvaluation n).hom.app T.obj) := by
  let := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let RX := reduction l E X
  let RY := reduction l E Y
  let EX : coefficientSequenceDerived l E X ⥤ X.proEtaleDerivedCategory A :=
    coefficientSequenceDerivedEvaluation l E X n
  let EY : coefficientSequenceDerived l E Y ⥤ Y.proEtaleDerivedCategory A :=
    coefficientSequenceDerivedEvaluation l E Y n
  let H := systemDerivedOpen l E c.i ⋙ systemDirect l E c.g
  let F := sfIntrinsicCompactSupport c A
  let DX := scalarReductionDerivedExtension l E X n
  let DY := scalarReductionDerivedExtension l E Y n
  let rX : RX ⋙ EX ≅ DX := ((models l E).system X).reductionEvaluation n
  let rY : RY ⋙ EY ≅ DY := ((models l E).system Y).reductionEvaluation n
  let d : H ⋙ EY ≅ EX ⋙ F :=
    compactEvaluation (l := l) (E := E) (f := f) (c := c) n
  change
      (sfCompactSupportFiniteReductionIso l K₀ hl c E T n).hom =
        rY.inv.app ((sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj T).obj ≫
          EY.map ((compactOperationReduction l E K₀ hl f c).app T) ≫
          d.hom.app (RX.obj T.obj) ≫ F.map (rX.hom.app T.obj)
  let τ := compactRealization l E K₀ hl f c
  let t := (operationReduction l E H).app T.obj
  let FT := (sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj T
  have hspec : CompactRealizationSpec l E K₀ hl f c τ := by
    unfold τ compactRealization
    exact (compactRealization_existsUnique l E K₀ hl f c).exists.choose_spec
  have h := hspec T n
  have hn := rY.inv.naturality (τ.hom.app T)
  dsimp only [Functor.comp_map] at hn
  erw [reassoc_of% hn] at h
  have ho : EY.map ((compactOperationReduction l E K₀ hl f c).app T) =
      EY.map (RY.map (τ.hom.app T)) ≫ EY.map t := by
    exact EY.map_comp _ _
  rw [ho]
  simpa only [A, EX, EY, F, RX, RY, rX, t, compactFiniteEvaluation, d, compactEvaluation,
    Iso.trans_hom, NatTrans.comp_app,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
    Functor.comp_obj, ObjectProperty.ι_obj, Category.assoc] using h.symm

omit [IsIso gX] [IsIso gY] in
private theorem compactCoordinateTransport
    (K : sfIntegralConstructibleCategory l E X) (n : ℕ)
    (a : (constructibleIntegralPullback l E gY).obj
        ((sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj K) ⟶
      (sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj
        ((constructibleIntegralPullback l E gX).obj K))
    (h : (reduction l E Y).map a.hom ≫
          (compactOperationReduction l E K₀ hl f c).app
            ((constructibleIntegralPullback l E gX).obj K) ≫
          (systemDerivedOpen l E c.i ⋙ systemDirect l E c.g).map
            ((reductionPullbackIso l E gX).hom.app K) =
        (reductionPullbackIso l E gY).hom.app
            ((sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj K) ≫
          (integralComparisonDerivedSequencePullback l E gY).map
            ((compactOperationReduction l E K₀ hl f c).app K) ≫
          (systemCompactExchange l E c gX gB gY wp sj).app
            ((reduction l E X).obj K.obj)) :
    (scalarReductionDerivedExtension l E Y n).map a.hom ≫
      (sfCompactSupportFiniteReductionIso l K₀ hl c E
        ((constructibleIntegralPullback l E gX).obj K) n).hom =
    compactFiniteCoordinates l E K₀ hl f c gX gB gY wp sj K n := by
  have hcoord := finiteCoordinateTransport
    (reduction l E X)
    (reduction l E Y)
    (coefficientSequenceDerivedEvaluation l E X n)
    (coefficientSequenceDerivedEvaluation l E Y n)
    (scalarReductionDerivedExtension l E X n)
    (scalarReductionDerivedExtension l E Y n)
    (systemDerivedOpen l E c.i ⋙ systemDirect l E c.g)
    (finiteSupportFunctor l E c n)
    (integralComparisonDerivedSequencePullback l E gX)
    (integralComparisonDerivedSequencePullback l E gY)
    (finitePullFunctor l E gX n)
    (finitePullFunctor l E gY n)
    (finiteReductionEvaluation l E (X := X) n)
    (finiteReductionEvaluation l E (X := Y) n)
    (compactEvaluation (l := l) (E := E) (f := f) (c := c) n)
    (finitePullEvaluation l E gX n) (finitePullEvaluation l E gY n)
    (finiteCompact l E (n + 1) (Nat.succ_pos n) c gX gB gY wp sj)
    (K := K.obj) (Q := ((constructibleIntegralPullback l E gX).obj K).obj)
    (U := ((constructibleIntegralPullback l E gY).obj
      ((sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj K)).obj)
    (V := ((sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj K).obj)
    (W := ((sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj
      ((constructibleIntegralPullback l E gX).obj K)).obj)
    (a := a.hom)
    (bX := (reductionPullbackIso l E gX).app K)
    (bY := (reductionPullbackIso l E gY).app
      ((sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj K))
    (oK := (compactOperationReduction l E K₀ hl f c).app K)
    (oQ := (compactOperationReduction l E K₀ hl f c).app
      ((constructibleIntegralPullback l E gX).obj K))
    (e := (systemCompactExchange l E c gX gB gY wp sj).app
      ((reduction l E X).obj K.obj))
    (kX := finitePullCoordinates l E gX K n)
    (kY := finitePullCoordinates l E gY
      ((sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj K) n)
    (sK := (sfCompactSupportFiniteReductionIso l K₀ hl c E K n).hom)
    (sQ := (sfCompactSupportFiniteReductionIso l K₀ hl c E
      ((constructibleIntegralPullback l E gX).obj K) n).hom)
    (hr := h)
    (he := compactExchange_tensor (l := l) (E := E) (f := f) (c := c)
      (gX := gX) (gB := gB) (gY := gY) (wp := wp) (sj := sj) n
      ((reduction l E X).obj K.obj))
    (hsK := compactFiniteReduction_coordinates (l := l) (E := E) (K₀ := K₀)
      (hl := hl) (f := f) (c := c) K n)
    (hsQ := compactFiniteReduction_coordinates (l := l) (E := E) (K₀ := K₀)
      (hl := hl) (f := f) (c := c) ((constructibleIntegralPullback l E gX).obj K) n)
    (hkX := finitePullCoordinates_hom l E gX K n)
    (hkY := finitePullCoordinates_hom l E gY
      ((sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj K) n)
  simpa -implicitDefEqProofs only [compactFiniteCoordinates, finiteSupportFunctor,
    finitePullFunctor] using hcoord

/-- The realized system exchange has the finite proper/open coordinates.
Source: blueprint compact-support transport, Steps 2 and 5; projection-normalized
compact realization and `systemCompactExchange_evaluation`.
(blueprint: lem-pur-frobenius-compact-finite-coordinates).

Proof: evaluate the reduction-counit equation for the constructed integral exchange.
The compact realization spec supplies the finite-support comparison. Evaluation of
the system exchange gives the finite proper/open mate; naturality of the pullback
model changes its coordinates. Naturality of the operation evaluation and reduction
comparisons, followed by cancellation of the input coordinate isomorphism, gives
exactly the displayed word. This calculation does not detect system morphisms by
finite evaluation. -/
theorem compactIntegral_finiteCoordinates
    (K : sfIntegralConstructibleCategory l E X) (n : ℕ) :
    (scalarReductionDerivedExtension l E Y n).map
        (((compactIntegral l E K₀ hl f c gX gB gY wp sj).app K).hom) ≫
      (sfCompactSupportFiniteReductionIso l K₀ hl c E
        ((constructibleIntegralPullback l E gX).obj K) n).hom =
    compactFiniteCoordinates l E K₀ hl f c gX gB gY wp sj K n := by
  exact compactCoordinateTransport l E K₀ hl f c gX gB gY wp sj K n
    ((compactIntegral l E K₀ hl f c gX gB gY wp sj).app K)
    (compactIntegral_reduction l E K₀ hl f c gX gB gY wp sj K)

end Compact
end WeilConjectures.FrobeniusExchange
