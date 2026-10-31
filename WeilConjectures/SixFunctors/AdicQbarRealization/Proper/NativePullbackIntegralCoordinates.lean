/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativeProperCoefficientOperations
public import WeilConjectures.SixFunctors.AdicQbarRealization.Integral.AdicIntegralRealizationCoordinates

/-! # Integral coordinates for arbitrary native pullback

Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15.
(blueprint: lem-sf-native-pullback-integral-coordinates)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization.Proper
variable (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (p : X ⟶ Y)
  (R : LocallyFiniteAdicRealization.Realization l X)
  (S : LocallyFiniteAdicRealization.Realization l Y)
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  (O : Operations l p R S)
  (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
  (I : IntegralComparison l p R S O E)

/-- The finite native pullback map is inverse derived balance followed by the
specified ordinary-to-completed unit. Source: BS Remark 6.8.15.
(blueprint: lem-sf-native-pullback-integral-coordinates). -/
def nativePullbackIntegralMap
    (K : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) Y) :
    (ContinuousRational.derivedPull p O.coefficient).obj
        ((pbcDerivedExtend (coefficientMap l Y S E)).obj K.obj) ⟶
      (pbcDerivedExtend (coefficientMap l X R E)).obj
        ((constructibleIntegralPullback l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) p).obj K).obj :=
  I.derived.inv.app K.obj ≫
    (pbcDerivedExtend (coefficientMap l X R E)).map (I.completion K).hom

/-- Extract the native pullback equation in integral realization coordinates.
Source: BS Remark 6.8.15.
(blueprint: lem-sf-native-pullback-integral-coordinates).

Proof: compose the integral stage pullback identification and the given integral
realization into e. Let d be inverse derived balance followed by the specified
completion isomorphism, and f the pulled-back source realization. IntegralAgreement
says a = e d⁻¹ f⁻¹, including the literal raw-localization transports. Cancelling
a and d gives a⁻¹ e = f d, which is the displayed equation. This uses only
isomorphism cancellation and works for zero and torsion integral objects. -/
theorem nativePullbackIntegralCoordinates
    (a : commonStageDerivedPullback l (PadicAlgCl l) p ⋙ ordinary l X R ≅
      ordinary l Y S ⋙ ContinuousRational.derivedPull p O.coefficient)
    (ha : IntegralAgreement l p R S O E I a)
    (K : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) Y) :
    a.inv.app ((tensorStage l Y E).obj K) ≫
        (ordinary l X R).map (integralStagePullIso l p E K).hom ≫
        (integralCoordinateIso l X R E).hom.app ((constructibleIntegralPullback l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) p).obj K) =
      (ContinuousRational.derivedPull p O.coefficient).map
          ((integralCoordinateIso l Y S E).hom.app K) ≫
        nativePullbackIntegralMap l p R S O E I K := by
  let := R.commutative
  let := S.commutative
  let P := constructibleIntegralPullback l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) p
  let EX := pbcDerivedExtend (coefficientMap l X R E)
  let rX := (integralCoordinateIso l X R E).app (P.obj K)
  let rY := (integralCoordinateIso l Y S E).app K
  let e := (ordinary l X R).mapIso (integralStagePullIso l p E K) ≪≫ rX
  let d := (I.derived.app K.obj).symm ≪≫ EX.mapIso (I.completion K)
  let f := (ContinuousRational.derivedPull p O.coefficient).mapIso rY
  have h : (a.app ((tensorStage l Y E).obj K)).hom = e.hom ≫ d.inv ≫ f.inv := by
    simpa only [e, d, f, rX, rY, P, EX, Iso.trans_hom, Iso.trans_inv,
      integralStagePullIso, integralCoordinateIso, tensorStage, Functor.comp_obj,
      Functor.mapIso_hom, Functor.mapIso_inv, Iso.symm_hom, Iso.symm_inv,
      Iso.app_hom, Iso.app_inv, Functor.map_comp, Category.assoc] using eq_of_heq (ha K)
  have h' : (a.app ((tensorStage l Y E).obj K)).inv ≫ e.hom = f.hom ≫ d.hom := by
    apply (cancel_epi (a.app ((tensorStage l Y E).obj K)).hom).mp
    simp only [Iso.hom_inv_id_assoc]
    rw [h]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  simpa only [e, d, f, rX, rY, P, EX, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, nativePullbackIntegralMap, Iso.app_hom, Iso.app_inv,
    Category.assoc] using h'

end WeilConjectures.AdicQbarRealization.Proper
