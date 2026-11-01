/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Integral.AdicIntegralTensorCoordinates

/-! # Typed integral realization coordinates

This is the given integral realization comparison, with the coefficient map and
common-stage inclusion named explicitly. Source: BS 6.8.14--6.8.15; HRS 7.9.
(blueprint: def-sf-adic-integral-realization-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option cleanup.letToHave false
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization

/-- The specified integral realization isomorphism, in finite tensor coordinates.
Source: BS 6.8.14--6.8.15 (blueprint: def-sf-adic-integral-realization-coordinates). -/
def integralCoordinateIso (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (R : LocallyFiniteAdicRealization.Realization l X)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l)) :
    tensorStage l X E ⋙ ordinary l X R ≅
      (sfIntegralConstructible l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).ι ⋙
        pbcDerivedExtend (coefficientMap l X R E) := by
  letI := R.commutative
  exact R.integral E

variable (l : ℕ) [Fact l.Prime]

private theorem inverse_coordinates {A : Type*} [Category* A]
    {a b x y : A} (c : a ≅ b) (e : a ≅ x) (d : y ≅ x) (f : b ≅ y)
    (h : c.hom = e.hom ≫ d.inv ≫ f.inv) : c.inv ≫ e.hom = f.hom ≫ d.hom := by
  apply (cancel_epi c.hom).mp
  simp only [Iso.hom_inv_id_assoc]
  rw [h]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

/-- Extract the finite tensor coordinate equation from its specified normalization.
Source: BS 6.8.14--6.8.15
(blueprint: def-sf-adic-integral-realization-coordinates). -/
theorem finite_tensor_coordinates (X : Scheme.{u})
    (R : LocallyFiniteAdicRealization.Realization l X)
    [∀ x : X, Invertible (l : X.residueField x)] (A : At l X R)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (N : FiniteNormalization l X R A E)
    (K L : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X) :
    let TY := constructibleIntegralTensor l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X
    let J := tensorStage l X E
    let F := ordinary l X R
    A.tensor.hom.app (J.obj K, J.obj L) ≫
        F.map (integralStageTensorIso l X E K L).inv ≫
        (integralCoordinateIso l X R E).hom.app (TY.obj (K, L)) =
      A.closed.tensor.map (Prod.mkHom ((integralCoordinateIso l X R E).hom.app K)
        ((integralCoordinateIso l X R E).hom.app L)) ≫ finiteIntegralTensorMap l X R A E N K L := by
  let := R.commutative
  have h : A.tensor.hom.app ((tensorStage l X E).obj K, (tensorStage l X E).obj L) =
      A.closed.tensor.map (Prod.mkHom ((integralCoordinateIso l X R E).hom.app K)
        ((integralCoordinateIso l X R E).hom.app L)) ≫ finiteIntegralTensorMap l X R A E N K L ≫
      (integralCoordinateIso l X R E).inv.app
        ((constructibleIntegralTensor l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj (K, L)) ≫
      (ordinary l X R).map (integralStageTensorIso l X E K L).hom := by
    simpa only [finiteIntegralTensorMap, integralStageTensorIso, tensorQuotientIso,
      tensorIntegralObjectIso, tensorStage, integralCoordinateIso, asIso_hom, Functor.comp_obj,
      Iso.trans_hom,
      Functor.mapIso_hom, Iso.symm_hom, Functor.map_comp, Category.assoc] using
      eq_of_heq (N.integral_tensor K L)
  dsimp only
  rw [h]
  simp only [Category.assoc, Iso.map_hom_inv_id_assoc,
    Iso.inv_hom_id_app]
  erw [Category.comp_id]

/-- Extract the integral pullback coordinate equation from its specified normalization.
Source: BS 6.8.14--6.8.15
(blueprint: def-sf-adic-integral-realization-coordinates). -/
theorem integral_pull_coordinates {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (R : LocallyFiniteAdicRealization.Realization l X)
    (S : LocallyFiniteAdicRealization.Realization l Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (B : RingReindex l X g R S)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (V : IntegralReindex l X g B E)
    (c : commonStageDerivedPullback l (PadicAlgCl l) g ⋙ ordinary l X R ≅
      ordinary l Y S ⋙ derivedPull l X g B)
    (hc : integralRealizationAgreement l g R S B E V c)
    (K : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) Y) :
    c.inv.app ((tensorStage l Y E).obj K) ≫
        (ordinary l X R).map (integralStagePullIso l g E K).hom ≫
        (integralCoordinateIso l X R E).hom.app ((constructibleIntegralPullback l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) g).obj K) =
      (derivedPull l X g B).map ((integralCoordinateIso l Y S E).hom.app K) ≫
        finiteIntegralPullMap l g R S B E V K := by
  let := R.commutative
  let := S.commutative
  let P := constructibleIntegralPullback l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) g
  let EX := pbcDerivedExtend (coefficientMap l X R E)
  let rX := (integralCoordinateIso l X R E).app (P.obj K)
  let rY := (integralCoordinateIso l Y S E).app K
  let e := (ordinary l X R).mapIso (integralStagePullIso l g E K) ≪≫ rX
  let d := V.derived.app K.obj ≪≫ EX.mapIso (podCompletedToTowerIso l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) g K)
  let f := (derivedPull l X g B).mapIso rY
  have h : (c.app ((tensorStage l Y E).obj K)).hom = e.hom ≫ d.inv ≫ f.inv := by
    simpa only [e, d, f, rX, rY, P, EX, Iso.trans_hom, Iso.trans_inv,
      integralStagePullIso, integralCoordinateIso, tensorStage, Functor.comp_obj,
      Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv,
      Functor.map_comp, Category.assoc] using
      eq_of_heq (hc K)
  have h' := inverse_coordinates (c.app ((tensorStage l Y E).obj K)) e d f h
  simpa only [e, d, f, rX, rY, P, EX, Iso.trans_hom, Functor.mapIso_hom,
    finiteIntegralPullMap, Iso.app_hom, Iso.app_inv, Category.assoc] using h'

end WeilConjectures.AdicQbarRealization
