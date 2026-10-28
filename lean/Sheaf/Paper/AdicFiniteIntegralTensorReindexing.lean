/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.AdicIntegralTensorCoordinates

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
  sorry

end WeilConjectures.AdicQbarRealization
