/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.AdicRealizationFamilyData
public import WeilConjectures.SixFunctors.AdicQbarRealization.Completed.AdicCompletedTensorFiniteModels

/-! # Integral coordinates for the realization tensor square

All four maps are composites of the previously specified comparisons.
Source: BS Proposition 6.8.14 and Remark 6.8.15; HRS Lemma 7.9.
(blueprint: def-sf-adic-integral-tensor-coordinates).
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

/-- The finite tensor map is balanced multiplication followed by the specified
ordinary-to-completed tensor comparison. No common-stage realization occurs.
Source: BS 6.8.15 (blueprint: def-sf-adic-integral-tensor-coordinates). -/
def finiteIntegralTensorMap (X : Scheme.{u})
    (R : LocallyFiniteAdicRealization.Realization l X)
    [∀ x : X, Invertible (l : X.residueField x)] (A : At l X R)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (N : FiniteNormalization l X R A E)
    (K L : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X) :
    A.closed.tensor.obj
      ((pbcDerivedExtend (coefficientMap l X R E)).obj K.obj,
       (pbcDerivedExtend (coefficientMap l X R E)).obj L.obj) ⟶
    (pbcDerivedExtend (coefficientMap l X R E)).obj
      ((constructibleIntegralTensor l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj
        (K, L)).obj :=
  N.ordinary.inv.app (K.obj, L.obj) ≫
    (pbcDerivedExtend (coefficientMap l X R E)).map
      (N.completion.comparison.app (K.obj, L.obj))

/-- Scalar base change, followed by the canonical complete-input identification
with the tower-defined integral pullback.
Source: BS 6.8.15 (blueprint: def-sf-adic-integral-tensor-coordinates). -/
def finiteIntegralPullMap {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (R : LocallyFiniteAdicRealization.Realization l X)
    (S : LocallyFiniteAdicRealization.Realization l Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (B : RingReindex l X g R S)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (V : IntegralReindex l X g B E)
    (K : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) Y) :
    (derivedPull l X g B).obj ((pbcDerivedExtend (coefficientMap l Y S E)).obj K.obj) ⟶
    (pbcDerivedExtend (coefficientMap l X R E)).obj
      ((constructibleIntegralPullback l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) g).obj K).obj :=
  V.derived.hom.app K.obj ≫
    (pbcDerivedExtend (coefficientMap l X R E)).map
      (podCompletedToTowerIso l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) g K).hom

/-- The literal object identifications for common-stage and raw rational pullback.
Source: the object clauses of the two pullback existence/uniqueness theorems.
(blueprint: def-sf-adic-integral-tensor-coordinates). -/
def integralStagePullIso {X Y : Scheme.{u}} (g : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (K : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) Y) :
    (commonStageDerivedPullback l (PadicAlgCl l) g).obj ((tensorStage l Y E).obj K) ≅
    (tensorStage l X E).obj ((constructibleIntegralPullback l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) g).obj K) :=
by
  let I := GeneralAlgebraicallyClosedCoefficients.inclusion
    (l := l) (Ω := PadicAlgCl l) (Y := X) E
  let IY := GeneralAlgebraicallyClosedCoefficients.inclusion
    (l := l) (Ω := PadicAlgCl l) (Y := Y) E
  let QX := sfRationalConstructibleLocalization l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X
  let QY := sfRationalConstructibleLocalization l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) Y
  let P := rationalDerivedPullback l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) g
  let PI := constructibleIntegralPullback l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) g
  let e : (commonStageDerivedPullback l (PadicAlgCl l) g).obj (IY.obj (QY.obj K)) ≅
      I.obj (P.obj (QY.obj K)) :=
    eqToIso ((commonStageDerivedPullback_existsUnique l (PadicAlgCl l) g).exists.choose_spec.1
      (IY.obj (QY.obj K)))
  let f : P.obj (QY.obj K) ≅ QX.obj (PI.obj K) :=
    eqToIso ((rationalDerivedPullback_existsUnique l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) g).exists.choose_spec.2.1
      (QY.obj K))
  exact e ≪≫ I.mapIso f

/-- The inclusion tensorator with its raw rational object identification inserted.
Source: BS 6.8.15 (blueprint: def-sf-adic-integral-tensor-coordinates). -/
def integralStageTensorIso (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)]
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (K L : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X) :
    (tensorStage l X E).obj ((constructibleIntegralTensor l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj (K, L)) ≅
    (commonStageDerivedTensor l (PadicAlgCl l) X).obj
      ((tensorStage l X E).obj K, (tensorStage l X E).obj L) :=
  (GeneralAlgebraicallyClosedCoefficients.inclusion
    (l := l) (Ω := PadicAlgCl l) (Y := X) E).mapIso
      (tensorIntegralObjectIso l X E K L).symm ≪≫
  stageTensor l X (PadicAlgCl l) E
    ((sfRationalConstructibleLocalization l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj K)
    ((sfRationalConstructibleLocalization l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).obj L)

end WeilConjectures.AdicQbarRealization
