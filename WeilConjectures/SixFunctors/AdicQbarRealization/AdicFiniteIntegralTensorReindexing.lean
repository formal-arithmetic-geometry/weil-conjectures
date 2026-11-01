/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Integral.AdicIntegralTensorCoordinates
import WeilConjectures.SixFunctors.AdicQbarRealization.Tensor.AdicTensorPresentationComparison
import WeilConjectures.SixFunctors.AdicQbarRealization.AdicOrdinaryScalarTensorReindexing
import WeilConjectures.SixFunctors.AdicQbarRealization.Tensor.AdicTensorCompletionReindexing

/-! # The finite integral scalar-extension tensor square

Source: BS Definition 3.4.10, Proposition 6.8.14 and Remark 6.8.15; HRS Lemma 7.9.
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
variable (l : ℕ) [Fact l.Prime]

attribute [local irreducible] tensorPresentationComparison tensorPresentationCompletion
  finiteAmbientScalarTensor podCompletedAmbientTensor pullbackTensorCalculus
  podCompletedDerivedInverseImage derivedPull coefficientMap
  integralCompletedTensor finiteIntegralTensorMap finiteIntegralPullMap
  canonicalIntegralPullbackTensor reductionDerivedChange

/-- Scalar base change respects the normalized completed tensor on one integral
coefficient field. The displayed equation uses only ordinary scalar extension and integral
operations; neither a common-stage tensorator nor a realization comparison occurs in it.
Source: BS Definition 3.4.10, Lemma 6.5.5 and Remark 6.8.15; HRS Lemma 7.9.
(blueprint: lem-sf-adic-finite-integral-tensor-reindexing).

Proof: choose flat-term K-flat representatives of K and L. Apply the representative
identities of NX, NY and V and the representative identity of W. The ordinary chain
square is checked on homogeneous pure sections: the two balanced scalar comparisons
and W.pure send a scalar times x tensor y to the same generator after applying B.iso.
The identity B.functions identifies the scalar action with the completed integral
coefficient action. Tensor induction and the coproduct universal property extend this
to all terms; the Koszul differential is preserved termwise. For the completion map,
use NX.completion.normalized and NY.completion.normalized: the product coordinates are
the quotient maps on pure sections and the shifted mapping-fiber coordinates are zero.
Reindexing preserves both coordinates and every quotient transition, so equality holds
for the whole completion map. Pass to the derived category using the representative
identities and cancel the K-flat counits. The canonical integral pullback/tensor map is
the limit of these quotient comparisons, conjugated by its specified coherent counits;
podCompletedToTowerIso supplies exactly those complete-input identifications. This
gives the displayed square. The argument also applies to zero complexes and torsion
integral objects; no invertibility of the uniformizer or faithfulness of rationalization
is used. -/
theorem finite_integral_tensor_reindexing
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (R : LocallyFiniteAdicRealization.Realization l X)
    (S : LocallyFiniteAdicRealization.Realization l Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (A : At l X R) (C : At l Y S) (B : RingReindex l X g R S)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (NX : FiniteNormalization l X R A E) (NY : FiniteNormalization l Y S C E)
    (V : IntegralReindex l X g B E) (W : ReindexTensor l X g A C B)
    (K L : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) Y) :
    let P := constructibleIntegralPullback l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) g
    let TY := constructibleIntegralTensor l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) Y
    let EX := pbcDerivedExtend (coefficientMap l X R E)
    let EY := pbcDerivedExtend (coefficientMap l Y S E)
    let F := derivedPull l X g B
    F.map (finiteIntegralTensorMap l Y S C E NY K L) ≫
        finiteIntegralPullMap l g R S B E V (TY.obj (K, L)) ≫
        EX.map (canonicalIntegralPullbackTensor l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) g K L).hom.hom =
      W.tensor.hom.app (EY.obj K.obj, EY.obj L.obj) ≫
        A.closed.tensor.map (Prod.mkHom
          (finiteIntegralPullMap l g R S B E V K)
          (finiteIntegralPullMap l g R S B E V L)) ≫
        finiteIntegralTensorMap l X R A E NX (P.obj K) (P.obj L) := by
  let k := AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E
  let EX := pbcDerivedExtend (coefficientMap l X R E)
  let EY := pbcDerivedExtend (coefficientMap l Y S E)
  let F := derivedPull l X g B
  let H := podCompletedDerivedInverseImage l k g
  let P := constructibleIntegralPullback l k g
  let TX := (pullbackTensorCalculus l k X).integralClosed.tensor
  let TY := (pullbackTensorCalculus l k Y).integralClosed.tensor
  let UY := constructibleIntegralTensor l k Y
  let tY := (tensorPresentationCompletion l k Y NY.completion).app (K.obj, L.obj)
  let tX := (tensorPresentationCompletion l k X NX.completion).app
    ((P.obj K).obj, (P.obj L).obj)
  let sY := (finiteAmbientScalarTensor l Y S C E NY).inv.app (K.obj, L.obj)
  let sX := (finiteAmbientScalarTensor l X R A E NX).inv.app
    (H.obj K.obj, H.obj L.obj)
  let sX' := (finiteAmbientScalarTensor l X R A E NX).inv.app
    ((P.obj K).obj, (P.obj L).obj)
  let iK := (podCompletedToTowerIso l k g K).hom
  let iL := (podCompletedToTowerIso l k g L).hom
  let iT := (podCompletedToTowerIso l k g (UY.obj (K, L))).hom
  let n := (canonicalIntegralPullbackTensor l k g K L).hom.hom
  let m := (podCompletedAmbientTensor l k g).hom.app (K.obj, L.obj)
  have ho := ordinary_scalar_tensor_reindexing l g R S A C B E NX NY V W K.obj L.obj
  change F.map sY ≫ V.derived.hom.app (TY.obj (K.obj, L.obj)) ≫ EX.map m =
    W.tensor.hom.app (EY.obj K.obj, EY.obj L.obj) ≫
      A.closed.tensor.map (Prod.mkHom (V.derived.hom.app K.obj) (V.derived.hom.app L.obj)) ≫
      sX at ho
  have hc := tensor_completion_reindexing l k g NX.completion NY.completion K L
  change H.map tY ≫ iT ≫ n = m ≫ TX.map (Prod.mkHom iK iL) ≫ tX at hc
  have hv := V.derived.hom.naturality tY
  change F.map (EY.map tY) ≫ V.derived.hom.app (UY.obj (K, L)).obj =
    V.derived.hom.app (TY.obj (K.obj, L.obj)) ≫ EX.map (H.map tY) at hv
  have hs := (finiteAmbientScalarTensor l X R A E NX).inv.naturality
    (Prod.mkHom iK iL)
  change A.closed.tensor.map (Prod.mkHom (EX.map iK) (EX.map iL)) ≫ sX' =
    sX ≫ EX.map (TX.map (Prod.mkHom iK iL)) at hs
  have fY := finiteIntegralTensorMap_factor l Y S C E NY K L
  change finiteIntegralTensorMap l Y S C E NY K L = sY ≫ EY.map tY at fY
  have fX := finiteIntegralTensorMap_factor l X R A E NX (P.obj K) (P.obj L)
  change finiteIntegralTensorMap l X R A E NX (P.obj K) (P.obj L) =
    sX' ≫ EX.map tX at fX
  unfold finiteIntegralPullMap
  change F.map (finiteIntegralTensorMap l Y S C E NY K L) ≫
      (V.derived.hom.app (UY.obj (K, L)).obj ≫ EX.map iT) ≫ EX.map n =
    W.tensor.hom.app (EY.obj K.obj, EY.obj L.obj) ≫
      A.closed.tensor.map (Prod.mkHom
        (V.derived.hom.app K.obj ≫ EX.map iK)
        (V.derived.hom.app L.obj ≫ EX.map iL)) ≫
      finiteIntegralTensorMap l X R A E NX (P.obj K) (P.obj L)
  simp only [fY, fX]
  calc
    _ = F.map sY ≫ V.derived.hom.app (TY.obj (K.obj, L.obj)) ≫
        EX.map (H.map tY ≫ iT ≫ n) := by
      simpa only [Functor.map_comp, Category.assoc] using
        congrArg (fun z ↦ F.map sY ≫ z ≫ EX.map iT ≫ EX.map n) hv
    _ = F.map sY ≫ V.derived.hom.app (TY.obj (K.obj, L.obj)) ≫
        EX.map m ≫ EX.map (TX.map (Prod.mkHom iK iL)) ≫ EX.map tX := by
      simpa only [Functor.map_comp, Category.assoc] using
        congrArg (fun z ↦ F.map sY ≫
          V.derived.hom.app (TY.obj (K.obj, L.obj)) ≫ EX.map z) hc
    _ = W.tensor.hom.app (EY.obj K.obj, EY.obj L.obj) ≫
        A.closed.tensor.map (Prod.mkHom (V.derived.hom.app K.obj)
          (V.derived.hom.app L.obj)) ≫ sX ≫
          EX.map (TX.map (Prod.mkHom iK iL)) ≫ EX.map tX := by
      simpa only [Category.assoc] using congrArg
        (fun z ↦ z ≫ EX.map (TX.map (Prod.mkHom iK iL)) ≫ EX.map tX) ho
    _ = W.tensor.hom.app (EY.obj K.obj, EY.obj L.obj) ≫
        A.closed.tensor.map (Prod.mkHom (V.derived.hom.app K.obj)
          (V.derived.hom.app L.obj)) ≫
          A.closed.tensor.map (Prod.mkHom (EX.map iK) (EX.map iL)) ≫ sX' ≫ EX.map tX := by
      simpa only [Category.assoc] using congrArg
        (fun z ↦ W.tensor.hom.app (EY.obj K.obj, EY.obj L.obj) ≫
          A.closed.tensor.map (Prod.mkHom (V.derived.hom.app K.obj)
            (V.derived.hom.app L.obj)) ≫ z ≫ EX.map tX) hs.symm
    _ = _ := by
      simp only [← Category.assoc, ← Functor.map_comp]
      rfl

end WeilConjectures.AdicQbarRealization
