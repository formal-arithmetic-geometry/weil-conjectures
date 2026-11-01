/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativePullbackIntegralCoordinates
public import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativePullbackTensorDescent
import WeilConjectures.SixFunctors.AdicQbarRealization.Integral.AdicIntegralStagePullTensor
import WeilConjectures.SixFunctors.AdicQbarRealization.Integral.AdicIntegralTensorPasting

/-! # Pasting the finite native tensor square through realization coordinates

Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15.
(blueprint: lem-sf-native-pullback-finite-tensor-descent)
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
  (O : Operations l p R S) (A : At l X R) (B : At l Y S)
  (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
  (NX : FiniteNormalization l X R A E) (NY : FiniteNormalization l Y S B E)
  (I : IntegralComparison l p R S O E) (W : TensorComparison l p R S O A B)

/-- The completed integral tensor square at one coefficient field. This contains
no common-stage realization comparison. Source: BS Remark 6.8.15.
(blueprint: lem-sf-native-pullback-finite-tensor-descent). -/
def NativePullbackFiniteTensorSquare : Prop :=
  ∀ K L : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) Y,
    let P := constructibleIntegralPullback l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) p
    let TY := constructibleIntegralTensor l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) Y
    let EX := pbcDerivedExtend (coefficientMap l X R E)
    let EY := pbcDerivedExtend (coefficientMap l Y S E)
    let F := ContinuousRational.derivedPull p O.coefficient
    F.map (finiteIntegralTensorMap l Y S B E NY K L) ≫
        nativePullbackIntegralMap l p R S O E I (TY.obj (K, L)) ≫
        EX.map (canonicalIntegralPullbackTensor l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) p K L).hom.hom =
      W.tensor.hom.app (EY.obj K.obj, EY.obj L.obj) ≫
        A.closed.tensor.map (Prod.mkHom (nativePullbackIntegralMap l p R S O E I K)
          (nativePullbackIntegralMap l p R S O E I L)) ≫
        finiteIntegralTensorMap l X R A E NX (P.obj K) (P.obj L)

attribute [local irreducible] ordinary coefficientMap integralCoordinateIso
  integralStagePullIso integralStageTensorIso finiteIntegralTensorMap nativePullbackIntegralMap

/-- The finite completed integral square implies the native realization tensor
square on its integral representatives. Source: BS Remark 6.8.15.
(blueprint: lem-sf-native-pullback-finite-tensor-descent).

Proof: express the two given realization tensorators using their finite normalized
coordinates. IntegralAgreement gives the three pullback coordinate equations, for
K, L, and their tensor. The canonical common-stage pullback/tensor comparison is
identified with the integral one by integral_stage_pull_tensor. Naturality of the
integral realization moves its integral tensor comparison to the end. Paste these
equations with the assumed completed integral square. Cancel the final coordinate
isomorphism; every cancelled map is an isomorphism. This is a categorical calculation
and also applies to zero and torsion inputs. -/
theorem nativePullbackFiniteTensorDescent
    (a : commonStageDerivedPullback l (PadicAlgCl l) p ⋙ ordinary l X R ≅
      ordinary l Y S ⋙ ContinuousRational.derivedPull p O.coefficient)
    (ha : IntegralAgreement l p R S O E I a)
    (hfinite : NativePullbackFiniteTensorSquare l p R S O A B E NX NY I W)
    (K L : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) Y) :
    NativePullbackTensorEquation l p R S O A B W a
      ((tensorStage l Y E).obj K) ((tensorStage l Y E).obj L) := by
  let P := constructibleIntegralPullback l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) p
  let TY := constructibleIntegralTensor l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) Y
  let TX := constructibleIntegralTensor l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X
  let JY := tensorStage l Y E
  let JX := tensorStage l X E
  let SY := commonStageDerivedTensor l (PadicAlgCl l) Y
  let SX := commonStageDerivedTensor l (PadicAlgCl l) X
  let G := commonStageDerivedPullback l (PadicAlgCl l) p
  let F := ContinuousRational.derivedPull p O.coefficient
  let RY := ordinary l Y S
  let RX := ordinary l X R
  let EX := pbcDerivedExtend (coefficientMap l X R E)
  let EY := pbcDerivedExtend (coefficientMap l Y S E)
  let aY := integralStageTensorIso l Y E K L
  let aX := integralStageTensorIso l X E (P.obj K) (P.obj L)
  let pK := integralStagePullIso l p E K
  let pL := integralStagePullIso l p E L
  let pT := integralStagePullIso l p E (TY.obj (K, L))
  let rYT := (integralCoordinateIso l Y S E).app (TY.obj (K, L))
  let rXPT := (integralCoordinateIso l X R E).app (P.obj (TY.obj (K, L)))
  let rXT := (integralCoordinateIso l X R E).app (TX.obj (P.obj K, P.obj L))
  let m := canonicalCommonStagePullbackTensor l (PadicAlgCl l) p
    (JY.obj K) (JY.obj L)
  let n := canonicalIntegralPullbackTensor l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) p K L
  let bY := finiteIntegralTensorMap l Y S B E NY K L
  let bX := finiteIntegralTensorMap l X R A E NX (P.obj K) (P.obj L)
  let d (H) := nativePullbackIntegralMap l p R S O E I H
  let rY (H) := (integralCoordinateIso l Y S E).app H
  let rX (H) := (integralCoordinateIso l X R E).app (P.obj H)
  have hTY := finite_tensor_coordinates l Y S B E NY K L
  have hTX := finite_tensor_coordinates l X R A E NX (P.obj K) (P.obj L)
  change B.tensor.hom.app (JY.obj K, JY.obj L) ≫ RY.map aY.inv ≫ rYT.hom =
    B.closed.tensor.map (Prod.mkHom (rY K).hom (rY L).hom) ≫ bY at hTY
  change A.tensor.hom.app (JX.obj (P.obj K), JX.obj (P.obj L)) ≫ RX.map aX.inv ≫
    rXT.hom = A.closed.tensor.map (Prod.mkHom (rX K).hom (rX L).hom) ≫ bX at hTX
  have hp (H) := nativePullbackIntegralCoordinates l p R S O E I a ha H
  have hpK : a.inv.app (JY.obj K) ≫ RX.map pK.hom ≫ (rX K).hom =
      F.map (rY K).hom ≫ d K := hp K
  have hpL : a.inv.app (JY.obj L) ≫ RX.map pL.hom ≫ (rX L).hom =
      F.map (rY L).hom ≫ d L := hp L
  have hpT : a.inv.app (JY.obj (TY.obj (K, L))) ≫ RX.map pT.hom ≫ rXPT.hom =
      F.map rYT.hom ≫ d (TY.obj (K, L)) := hp (TY.obj (K, L))
  have hs := integral_stage_pull_tensor l p E K L
  change G.map aY.hom ≫ m.hom ≫ SX.map (Prod.mkHom pK.hom pL.hom) =
    pT.hom ≫ JX.map n.hom ≫ aX.hom at hs
  have hs' : m.hom ≫ SX.map (Prod.mkHom pK.hom pL.hom) ≫ aX.inv =
      G.map aY.inv ≫ pT.hom ≫ JX.map n.hom := by
    apply (cancel_epi (G.map aY.hom)).mp
    simpa only [Category.assoc, Iso.map_hom_inv_id_assoc,
      Iso.hom_inv_id, Category.comp_id] using congrArg (fun z ↦ z ≫ aX.inv) hs
  have hn := (integralCoordinateIso l X R E).hom.naturality n.hom
  change RX.map (JX.map n.hom) ≫ rXT.hom = rXPT.hom ≫ EX.map n.hom.hom at hn
  have htail : RX.map m.hom ≫ RX.map (SX.map (Prod.mkHom pK.hom pL.hom)) ≫
      RX.map aX.inv ≫ rXT.hom =
      RX.map (G.map aY.inv) ≫ RX.map pT.hom ≫ rXPT.hom ≫ EX.map n.hom.hom := by
    have h := congrArg (fun z ↦ RX.map z ≫ rXT.hom) hs'
    simpa only [Functor.map_comp, Category.assoc, hn] using h
  have hf := hfinite K L
  change F.map bY ≫ d (TY.obj (K, L)) ≫ EX.map n.hom.hom =
    W.tensor.hom.app (EY.obj K.obj, EY.obj L.obj) ≫
      A.closed.tensor.map (Prod.mkHom (d K) (d L)) ≫ bX at hf
  let q := RX.map (SX.map (Prod.mkHom pK.hom pL.hom)) ≫ RX.map aX.inv ≫ rXT.hom
  have : IsIso q := by
    change IsIso ((RX.mapIso (SX.mapIso (Iso.prod pK pL)) ≪≫
      RX.mapIso aX.symm ≪≫ rXT).hom)
    infer_instance
  have hcNat := a.inv.naturality aY.inv
  change F.map (RY.map aY.inv) ≫ a.inv.app (JY.obj (TY.obj (K, L))) =
    a.inv.app (SY.obj (JY.obj K, JY.obj L)) ≫ RX.map (G.map aY.inv) at hcNat
  have hANat := A.tensor.hom.naturality (Prod.mkHom pK.hom pL.hom)
  change A.closed.tensor.map (Prod.mkHom (RX.map pK.hom) (RX.map pL.hom)) ≫
      A.tensor.hom.app (JX.obj (P.obj K), JX.obj (P.obj L)) =
    A.tensor.hom.app (G.obj (JY.obj K), G.obj (JY.obj L)) ≫
      RX.map (SX.map (Prod.mkHom pK.hom pL.hom)) at hANat
  have h := pasteIntegralTensorSquare F B.closed.tensor A.closed.tensor W.tensor
    (rYK := rY K) (rYL := rY L) (rYT := rYT)
    (rXK := rX K) (rXL := rX L) (rXT := rXT) (rXPT := rXPT)
    (μY := B.tensor.hom.app (JY.obj K, JY.obj L)) (aY := RY.map aY.inv)
    (cS := a.inv.app (SY.obj (JY.obj K, JY.obj L)))
    (cT := a.inv.app (JY.obj (TY.obj (K, L))))
    (m := RX.map m.hom) (aG := RX.map (G.map aY.inv))
    (pT := RX.map pT.hom) (ν := EX.map n.hom.hom)
    (pK := RX.map pK.hom) (pL := RX.map pL.hom)
    (cK := a.inv.app (JY.obj K)) (cL := a.inv.app (JY.obj L))
    (sP := RX.map (SX.map (Prod.mkHom pK.hom pL.hom)))
    (μXG := A.tensor.hom.app (G.obj (JY.obj K), G.obj (JY.obj L)))
    (μXJ := A.tensor.hom.app (JX.obj (P.obj K), JX.obj (P.obj L)))
    (aX := RX.map aX.inv) (bY := bY) (bX := bX)
    (dT := d (TY.obj (K, L))) (dK := d K) (dL := d L)
    hTY hTX htail hcNat hpT hf hANat hpK hpL
  simpa only [NativePullbackTensorEquation, F, G, RY, RX, JY, SY, m, tensorStage,
    Functor.comp_obj, Functor.prod_obj, Category.assoc] using h

end WeilConjectures.AdicQbarRealization.Proper
