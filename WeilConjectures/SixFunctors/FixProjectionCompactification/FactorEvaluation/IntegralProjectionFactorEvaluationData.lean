/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FixProjectionCompactification.ProjectionFactors.IntegralProjectionMiddleMap

/-! # Finite coordinates of the separate proper and open factors

Source: prop-sf-pf-coherence, compatibility with counits and extension by zero.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures.FixProjectionCompactification.FactorEvaluation
open IntegralSystemRealization

attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField integralDerivedPullback integralCompletedTensor
  pullbackTensorCalculus

variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
  (E : Type u) [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
  (S : SixFunctorOperationDatum D C E n hn)
  {X Y : SixFunctorSpace D} (f : X ⟶ Y) (c : Compactification f.hom.left) (m : ℕ)

/-- Natural finite direct-image comparison before the exchange-stage transport.
Source: coefficient directAdjunction and finiteDirectImage
(blueprint: def-sf-integral-projection-factor-evaluation-data). -/
def directIso :=
  Functor.isoWhiskerRight
      ((S.integralNormalization.reduction m).directAdjunction (identitySquare f c).p).right
      (intrinsicFiniteTorsionConstructible C.l E (m + 1)
        (Nat.le_add_left 1 m) Y.obj.left).ι ≪≫
    Functor.isoWhiskerLeft (sixFunctorIntegralReduction D C E m (identitySquare f c).Z)
      ((S.integralNormalization.finiteLevels m).finiteDirectImage (identitySquare f c).p)

/-- Natural finite open comparison before the exchange-stage transport.
Source: coefficient openExtension and finiteOpenExtension
(blueprint: def-sf-integral-projection-factor-evaluation-data). -/
def extensionIso :=
  Functor.isoWhiskerRight
      ((S.integralNormalization.reduction m).openExtension
        (identitySquare f c).i (identitySquare f c).open_i)
      (intrinsicFiniteTorsionConstructible C.l E (m + 1)
        (Nat.le_add_left 1 m) c.Z).ι ≪≫
    Functor.isoWhiskerLeft (sixFunctorIntegralReduction D C E m X)
      ((S.integralNormalization.finiteLevels m).finiteOpenExtension
        (identitySquare f c).i (identitySquare f c).open_i)

/-- Finite coordinates for the proper-image coefficient map.
Source: directAdjunction and finiteDirectImage in def-sf-operation-stages
(blueprint: def-sf-integral-projection-factor-evaluation-data). -/
def direct
    (M : sfIntegralConstructibleCategory C.l E (identitySquare f c).Z.obj.left) :
    (scalarReductionDerivedExtension C.l E Y.obj.left m).obj
        (((S.higher.integralExchange (identitySquare f c)).stage.properPush.obj M).obj) ≅
      (proEtaleConstantDerivedDirectImage c.g
        (Padic.coefficientExtensionRing C.l E (m + 1))).obj
          ((scalarReductionDerivedExtension C.l E c.Z m).obj M.obj) :=
  (scalarReductionDerivedExtension C.l E Y.obj.left m).mapIso (eqToIso (by
    rw [(S.higher.integralExchange (identitySquare f c)).properPush]
    rfl)) ≪≫
    (directIso D C E n hn S f c m).app M

/-- Finite coordinates for extension by zero.
Source: openExtension and finiteOpenExtension in def-sf-operation-stages
(blueprint: def-sf-integral-projection-factor-evaluation-data). -/
def extension
    (K : sfIntegralConstructibleCategory C.l E X.obj.left) :
    (scalarReductionDerivedExtension C.l E c.Z m).obj
        (((S.higher.integralExchange (identitySquare f c)).stage.openExtension.obj K).obj) ≅
      (sfIntrinsicExtensionByZero c.i
        (Padic.coefficientExtensionRing C.l E (m + 1))).mapDerivedCategory.obj
          ((scalarReductionDerivedExtension C.l E X.obj.left m).obj K.obj) :=
  (scalarReductionDerivedExtension C.l E c.Z m).mapIso (eqToIso (by
    rw [(S.higher.integralExchange (identitySquare f c)).openExtension]
    rfl)) ≪≫
    (extensionIso D C E n hn S f c m).app K

/-- Finite coordinates for the supplied compact-support comparison.
Source: supportAdjunction and finiteSupport in def-sf-operation-stages
(blueprint: def-sf-integral-projection-factor-evaluation-data). -/
def support
    (K : sfIntegralConstructibleCategory C.l E X.obj.left) :
    (scalarReductionDerivedExtension C.l E Y.obj.left m).obj
        (((S.higher.integral.support f c).obj K).obj) ≅
      (sixFunctorFiniteSupport D C E (m + 1) (Nat.le_add_left 1 m) f c).obj
        ((scalarReductionDerivedExtension C.l E X.obj.left m).obj K.obj) :=
  (intrinsicFiniteTorsionConstructible C.l E (m + 1)
    (Nat.le_add_left 1 m) Y.obj.left).ι.mapIso
      (((S.integralNormalization.reduction m).supportAdjunction f c).left.app K) ≪≫
    ((S.integralNormalization.finiteLevels m).finiteSupport f c).app
      ((sixFunctorIntegralReduction D C E m X).obj K)

end WeilConjectures.FixProjectionCompactification.FactorEvaluation
