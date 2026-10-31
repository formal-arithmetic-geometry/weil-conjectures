/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.AdicRealizationFamilyData

import WeilConjectures.SixFunctors.AdicQbarRealization.AdicFiniteIntegralTensorReindexing
import WeilConjectures.SixFunctors.AdicQbarRealization.Integral.AdicIntegralStagePullTensor
import WeilConjectures.SixFunctors.AdicQbarRealization.Integral.AdicIntegralRealizationCoordinates
import WeilConjectures.SixFunctors.AdicQbarRealization.Integral.AdicIntegralTensorPasting

/-! # Representative tensor square before cancellation

Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15;
Hemo--Richarz--Scholbach, Lemma 7.9. The statement is the representative
calculation after postcomposition with the inverse of the target tensorator.
(blueprint: lem-sf-adic-reindexing-tensor-integral-cancelled).
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
variable (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u})

attribute [local irreducible] ordinary coefficientMap integralCoordinateIso
  integralStagePullIso integralStageTensorIso finiteIntegralTensorMap finiteIntegralPullMap

/--
The normalized integral representative square, with the final realization
tensorator cancelled only after this equation is established.  This is the
finite K-flat, quotient-completion calculation in the proof of
`normalized_reindexing_tensor_integral`; the inverse tensorator is retained
explicitly so that the remaining theorem is a genuine cancellation step.
Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15, and
Hemo--Richarz--Scholbach, Lemma 7.9.
(blueprint: lem-sf-adic-reindexing-tensor-integral-cancelled).
-/
theorem normalized_reindexing_tensor_integral_cancelled
    (C : FamilyCore l D) (T U : GeometricSpace D) (g : T.base.left ≅ U.base.left)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (h_integral_normalization :
        letI := (C.data T).units
        letI := (C.data U).units
        integralRealizationAgreement l g.hom (C.data T).realization (C.data U).realization
          (C.ring T U g) E (C.integral T U g E) (C.comparison T U g)) :
    ∀ (K L : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) U.base.left),
    let I := GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := l) (Ω := PadicAlgCl l) (Y := U.base.left) E
    let Q := sfRationalConstructibleLocalization l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) U.base.left
    let M := I.obj (Q.obj K)
    let N := I.obj (Q.obj L)
    letI := (C.data T).units
    letI := (C.data U).units
    ((derivedPull l T.base.left g.hom (C.ring T U g)).map
        ((C.data U).tensor.tensor.hom.app (M, N)) ≫
      (C.comparison T U g).inv.app
        ((commonStageDerivedTensor l (PadicAlgCl l) U.base.left).obj (M, N)) ≫
      (ordinary l T.base.left (C.data T).realization).map
        (canonicalCommonStagePullbackTensor l (PadicAlgCl l) g.hom M N).hom) ≫
        (C.data T).tensor.tensor.inv.app
          ((commonStageDerivedPullback l (PadicAlgCl l) g.hom).obj M,
           (commonStageDerivedPullback l (PadicAlgCl l) g.hom).obj N) =
    ((C.pullTensor T U g).tensor.hom.app
        ((ordinary l U.base.left (C.data U).realization).obj M,
         (ordinary l U.base.left (C.data U).realization).obj N) ≫
      (C.data T).tensor.closed.tensor.map (Prod.mkHom
        ((C.comparison T U g).inv.app M) ((C.comparison T U g).inv.app N)) ≫
      (C.data T).tensor.tensor.hom.app
        ((commonStageDerivedPullback l (PadicAlgCl l) g.hom).obj M,
         (commonStageDerivedPullback l (PadicAlgCl l) g.hom).obj N) ≫
      (C.data T).tensor.tensor.inv.app
        ((commonStageDerivedPullback l (PadicAlgCl l) g.hom).obj M,
         (commonStageDerivedPullback l (PadicAlgCl l) g.hom).obj N)) := by
  intro K L
  let := (C.data T).units
  let := (C.data U).units
  let R := (C.data T).realization
  let S := (C.data U).realization
  let A := (C.data T).tensor
  let B := (C.data U).tensor
  let NX := (C.data T).finite E
  let NY := (C.data U).finite E
  let V := C.integral T U g E
  let W := C.pullTensor T U g
  let c := C.comparison T U g
  let P := constructibleIntegralPullback l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) g.hom
  let TY := constructibleIntegralTensor l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) U.base.left
  let TX := constructibleIntegralTensor l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) T.base.left
  let JY := tensorStage l U.base.left E
  let JX := tensorStage l T.base.left E
  let SY := commonStageDerivedTensor l (PadicAlgCl l) U.base.left
  let SX := commonStageDerivedTensor l (PadicAlgCl l) T.base.left
  let G := commonStageDerivedPullback l (PadicAlgCl l) g.hom
  let F := derivedPull l T.base.left g.hom (C.ring T U g)
  let RY := ordinary l U.base.left S
  let RX := ordinary l T.base.left R
  let EX := pbcDerivedExtend (coefficientMap l T.base.left R E)
  let EY := pbcDerivedExtend (coefficientMap l U.base.left S E)
  let aY := integralStageTensorIso l U.base.left E K L
  let aX := integralStageTensorIso l T.base.left E (P.obj K) (P.obj L)
  let pK := integralStagePullIso l g.hom E K
  let pL := integralStagePullIso l g.hom E L
  let pT := integralStagePullIso l g.hom E (TY.obj (K, L))
  let rYT := (integralCoordinateIso l U.base.left S E).app (TY.obj (K, L))
  let rXPT := (integralCoordinateIso l T.base.left R E).app (P.obj (TY.obj (K, L)))
  let rXT := (integralCoordinateIso l T.base.left R E).app (TX.obj (P.obj K, P.obj L))
  let m := canonicalCommonStagePullbackTensor l (PadicAlgCl l) g.hom
    (JY.obj K) (JY.obj L)
  let n := canonicalIntegralPullbackTensor l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) g.hom K L
  let bY := finiteIntegralTensorMap l U.base.left S B E NY K L
  let bX := finiteIntegralTensorMap l T.base.left R A E NX (P.obj K) (P.obj L)
  let d (H) := finiteIntegralPullMap l g.hom R S (C.ring T U g) E V H
  let rY (H) := (integralCoordinateIso l U.base.left S E).app H
  let rX (H) := (integralCoordinateIso l T.base.left R E).app (P.obj H)
  have hTY := finite_tensor_coordinates l U.base.left S B E NY K L
  have hTX := finite_tensor_coordinates l T.base.left R A E NX (P.obj K) (P.obj L)
  change B.tensor.hom.app (JY.obj K, JY.obj L) ≫ RY.map aY.inv ≫ rYT.hom =
    B.closed.tensor.map (Prod.mkHom (rY K).hom (rY L).hom) ≫ bY at hTY
  change A.tensor.hom.app (JX.obj (P.obj K), JX.obj (P.obj L)) ≫ RX.map aX.inv ≫
    rXT.hom = A.closed.tensor.map (Prod.mkHom (rX K).hom (rX L).hom) ≫ bX at hTX
  have hp (H) := integral_pull_coordinates l g.hom R S (C.ring T U g) E V c
    h_integral_normalization H
  have hpK : c.inv.app (JY.obj K) ≫ RX.map pK.hom ≫ (rX K).hom =
      F.map (rY K).hom ≫ d K := hp K
  have hpL : c.inv.app (JY.obj L) ≫ RX.map pL.hom ≫ (rX L).hom =
      F.map (rY L).hom ≫ d L := hp L
  have hpT : c.inv.app (JY.obj (TY.obj (K, L))) ≫ RX.map pT.hom ≫ rXPT.hom =
      F.map rYT.hom ≫ d (TY.obj (K, L)) := hp (TY.obj (K, L))
  have hs := integral_stage_pull_tensor l g.hom E K L
  change G.map aY.hom ≫ m.hom ≫ SX.map (Prod.mkHom pK.hom pL.hom) =
    pT.hom ≫ JX.map n.hom ≫ aX.hom at hs
  have hs' : m.hom ≫ SX.map (Prod.mkHom pK.hom pL.hom) ≫ aX.inv =
      G.map aY.inv ≫ pT.hom ≫ JX.map n.hom := by
    apply (cancel_epi (G.map aY.hom)).mp
    simpa only [Category.assoc, Iso.map_hom_inv_id_assoc,
      Iso.hom_inv_id, Category.comp_id] using congrArg (fun z ↦ z ≫ aX.inv) hs
  have hn := (integralCoordinateIso l T.base.left R E).hom.naturality n.hom
  change RX.map (JX.map n.hom) ≫ rXT.hom = rXPT.hom ≫ EX.map n.hom.hom at hn
  have htail : RX.map m.hom ≫ RX.map (SX.map (Prod.mkHom pK.hom pL.hom)) ≫
      RX.map aX.inv ≫ rXT.hom =
      RX.map (G.map aY.inv) ≫ RX.map pT.hom ≫ rXPT.hom ≫ EX.map n.hom.hom := by
    have h := congrArg (fun z ↦ RX.map z ≫ rXT.hom) hs'
    simpa only [Functor.map_comp, Category.assoc, hn] using h
  have hfinite := finite_integral_tensor_reindexing l g.hom R S A B (C.ring T U g)
    E NX NY V W K L
  change F.map bY ≫ d (TY.obj (K, L)) ≫ EX.map n.hom.hom =
    W.tensor.hom.app (EY.obj K.obj, EY.obj L.obj) ≫
      A.closed.tensor.map (Prod.mkHom (d K) (d L)) ≫ bX at hfinite
  let q := RX.map (SX.map (Prod.mkHom pK.hom pL.hom)) ≫ RX.map aX.inv ≫ rXT.hom
  have : IsIso q := by
    change IsIso ((RX.mapIso (SX.mapIso (Iso.prod pK pL)) ≪≫
      RX.mapIso aX.symm ≪≫ rXT).hom)
    infer_instance
  have hcNat := c.inv.naturality aY.inv
  change F.map (RY.map aY.inv) ≫ c.inv.app (JY.obj (TY.obj (K, L))) =
    c.inv.app (SY.obj (JY.obj K, JY.obj L)) ≫ RX.map (G.map aY.inv) at hcNat
  have hANat := A.tensor.hom.naturality (Prod.mkHom pK.hom pL.hom)
  change A.closed.tensor.map (Prod.mkHom (RX.map pK.hom) (RX.map pL.hom)) ≫
      A.tensor.hom.app (JX.obj (P.obj K), JX.obj (P.obj L)) =
    A.tensor.hom.app (G.obj (JY.obj K), G.obj (JY.obj L)) ≫
      RX.map (SX.map (Prod.mkHom pK.hom pL.hom)) at hANat
  have h := pasteIntegralTensorSquare F B.closed.tensor A.closed.tensor W.tensor
    (rYK := rY K) (rYL := rY L) (rYT := rYT)
    (rXK := rX K) (rXL := rX L) (rXT := rXT) (rXPT := rXPT)
    (μY := B.tensor.hom.app (JY.obj K, JY.obj L)) (aY := RY.map aY.inv)
    (cS := c.inv.app (SY.obj (JY.obj K, JY.obj L)))
    (cT := c.inv.app (JY.obj (TY.obj (K, L))))
    (m := RX.map m.hom) (aG := RX.map (G.map aY.inv))
    (pT := RX.map pT.hom) (ν := EX.map n.hom.hom)
    (pK := RX.map pK.hom) (pL := RX.map pL.hom)
    (cK := c.inv.app (JY.obj K)) (cL := c.inv.app (JY.obj L))
    (sP := RX.map (SX.map (Prod.mkHom pK.hom pL.hom)))
    (μXG := A.tensor.hom.app (G.obj (JY.obj K), G.obj (JY.obj L)))
    (μXJ := A.tensor.hom.app (JX.obj (P.obj K), JX.obj (P.obj L)))
    (aX := RX.map aX.inv) (bY := bY) (bX := bX)
    (dT := d (TY.obj (K, L))) (dK := d K) (dL := d L)
    hTY hTX htail hcNat hpT hfinite hANat hpK hpL
  have h' := congrArg (fun z ↦ z ≫ A.tensor.inv.app
    (G.obj (JY.obj K), G.obj (JY.obj L))) h
  simpa only [R, S, A, B, W, c, F, G, RY, RX, JY, SY, m, tensorStage,
    Functor.comp_obj, Functor.prod_obj, Category.assoc] using h'

end WeilConjectures.AdicQbarRealization
