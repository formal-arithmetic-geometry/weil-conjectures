/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.Paper.SmoothOrientationCoefficientFamily
public import Sheaf.Paper.SmoothOrientationTransportSquare
public import Sheaf.Paper.AdmissibleVerdierExchange
import all Sheaf.Paper.AdicPurityScalarNaturalityData

/-! # Site exchange comparisons under the smooth orientation

Source: latest blueprint, sec-six-functors/sk-thm-sf-package,
thm-pod-global-verdier-duality.proof.md, second paragraph
(blueprint: def-pod-integral-oriented-exchange-squares).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures

attribute [local instance 2000] IntermediateField.algebra'
attribute [local instance 2000] ConstructibleExceptionalCoefficients.category
attribute [local irreducible] CategoryTheory.Functor.mapIso CategoryTheory.Iso.trans
attribute [local irreducible]
  RationalSmoothPurityCanonical.integralIso
  RationalSmoothPurityCanonical.rationalIso
  RationalSmoothPurityCanonical.smallModelIso
  RationalSmoothPurityCanonical.commonIso
  RationalSmoothPurityCanonical.commonSourceComparison
  RationalSmoothPurityCanonical.sourceScalar

/-- Normalization of a reduction compact-support comparison against the actual
section-normalized comparison and the recorded reduction-presentation bridge.
Source: coefficient operations and adic reconstruction, counit reduction
(blueprint: def-pod-integral-oriented-exchange-squares). -/
@[irreducible] def smoothOrientationReductionSupportSquare
    (P : PurityFiniteSetting.{u}) {V W : Scheme.{u}}
    [V.Over (Spec (.of P.field.k))] [W.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (V ↘ Spec (.of P.field.k))]
    [QuasiCompact (V ↘ Spec (.of P.field.k))]
    [IsSeparated (V ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of P.field.k))]
    [QuasiCompact (W ↘ Spec (.of P.field.k))]
    [IsSeparated (W ↘ Spec (.of P.field.k))]
    (g : V ⟶ W) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (T : ConstructibleExceptionalCoefficients.System.{u, u} P.coefficients.l
      P.coefficients.Qbar P.field P.coefficients.different (f := g))
    (c : Compactification g)
    (E : AdicPurityScalarNaturality.Field P.field P.coefficients) (n : ℕ)
    (q : (T.ring.operation c (.integral
        (AdicPurityScalarNaturality.fieldStage P.field P.coefficients E))).F ⋙
        smoothIntegralOrientationReduction P E W n ≅
      smoothIntegralOrientationReduction P E V n ⋙
        (T.ring.operation c (.finite
          (AdicPurityScalarNaturality.fieldStage P.field P.coefficients E)
          ⟨n + 1, Nat.succ_pos n⟩)).F) : Prop :=
  let j := AdicPurityScalarNaturality.fieldStage P.field P.coefficients E
  let r : ℕ+ := ⟨n + 1, Nat.succ_pos n⟩
  let a := PurCompactSupport.reduction P.coefficients.l E.val r r.pos
  ∀ M,
    (finiteTorConstructible P.coefficients.l E.val r r.pos W).ι.map (q.hom.app M) ≫
      (T.ring.left c (.finite j r)).hom.app
        ((smoothIntegralOrientationReduction P E V n).obj M) ≫
      (PurCompactSupport.image (PurCompactSupport.finite P.coefficients.l E.val r r.pos) c).map
        ((AdicPurityScalarNaturality.reductionBridge P.field P.coefficients E V n).hom.app
          M.obj) =
    (AdicPurityScalarNaturality.reductionBridge P.field P.coefficients E W n).hom.app
        ((T.ring.operation c (.integral j)).F.obj M).obj ≫
      (pbcDerivedExtend (a.map W)).map ((T.ring.left c (.integral j)).hom.app M) ≫
        (PurCompactSupport.comparison a c).app M.obj

section CoefficientExchangeTransitions
variable (P : PurityFiniteSetting.{u}) {X : Scheme.{u}}
    [∀ x : X, Invertible (P.coefficients.l : X.residueField x)]
    [∀ y : Spec (.of P.field.k),
      Invertible (P.coefficients.l : (Spec (.of P.field.k)).residueField y)]
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [(Spec (.of P.field.k)).Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Spec (.of P.field.k) ↘ Spec (.of P.field.k))]
    [QuasiCompact (Spec (.of P.field.k) ↘ Spec (.of P.field.k))]
    [IsSeparated (Spec (.of P.field.k) ↘ Spec (.of P.field.k))]
    [(Spec (.of P.field.k) ↘ Spec (.of P.field.k)).IsOver (Spec (.of P.field.k))]
    (f : X ⟶ Spec (.of P.field.k)) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) [SmoothOfRelativeDimension d
      (f ≫ (Spec (.of P.field.k) ↘ Spec (.of P.field.k)))]
    (Sf : ConstructibleExceptionalCoefficients.System.{u, u} P.coefficients.l
      P.coefficients.Qbar P.field P.coefficients.different (f := f))
    (SY : ConstructibleExceptionalCoefficients.System.{u, u} P.coefficients.l
      P.coefficients.Qbar P.field P.coefficients.different
      (f := (Spec (.of P.field.k) ↘ Spec (.of P.field.k))))
    (SX : ConstructibleExceptionalCoefficients.System.{u, u} P.coefficients.l
      P.coefficients.Qbar P.field P.coefficients.different
      (f := f ≫ (Spec (.of P.field.k) ↘ Spec (.of P.field.k))))
    (p : AdmissibleVerdierExchange.Package P.coefficients.l P.coefficients.Qbar
      P.field P.coefficients.different f
      (Spec (.of P.field.k) ↘ Spec (.of P.field.k)) Sf SY SX
        (integralExceptionalCompactification P.field f)
        (integralExceptionalCompactification P.field
      (Spec (.of P.field.k) ↘ Spec (.of P.field.k))) (integralExceptionalCompactification P.field
      (f ≫ (Spec (.of P.field.k) ↘ Spec (.of P.field.k))))
      (AdmissibleVerdierExchange.admissible P.coefficients.l P.coefficients.Qbar
        P.field P.coefficients.different f
          (integralExceptionalCompactification P.field f)
          (integralExceptionalCompactification P.field
      (Spec (.of P.field.k) ↘ Spec (.of P.field.k))) (integralExceptionalCompactification P.field
      (f ≫ (Spec (.of P.field.k) ↘ Spec (.of P.field.k))))))

/-- Integral field-extension purity, exchange and oriented squares.
The support comparison is on the point, the dual maps transpose evaluation, and
orientation uses the inverse of the specified purity component.
Source: latest blueprint, global Verdier duality proof, coefficient passage
(blueprint: def-pod-integral-oriented-exchange-squares). -/
@[irreducible] def smoothIntegralExtensionExchangeSquares : Prop :=
  ∀ (J : AdicPurityScalarNaturality.Data P.field P.coefficients
      (f ≫ (Spec (.of P.field.k) ↘ Spec (.of P.field.k))) d SX)
    (E F : AdicPurityScalarNaturality.Field P.field P.coefficients) (h : E ≤ F)
    (M : ConstructibleExceptionalCoefficients.C.{u, u} P.coefficients.l
      P.coefficients.Qbar X (.integral
        (AdicPurityScalarNaturality.fieldStage P.field P.coefficients E)))
    (_hM : IsIntegralCoefficientSitePerfect P.coefficients.l E.val X M.obj)
    (hs : AdmissibleVerdierExchange.admissible P.coefficients.l P.coefficients.Qbar
      P.field P.coefficients.different f
        (integralExceptionalCompactification P.field f)
        (integralExceptionalCompactification P.field
      (Spec (.of P.field.k) ↘ Spec (.of P.field.k))) (integralExceptionalCompactification P.field
      (f ≫ (Spec (.of P.field.k) ↘ Spec (.of P.field.k)))) (.integral
        (AdicPurityScalarNaturality.fieldStage P.field P.coefficients E)))
    (ht : AdmissibleVerdierExchange.admissible P.coefficients.l P.coefficients.Qbar
      P.field P.coefficients.different f
        (integralExceptionalCompactification P.field f)
        (integralExceptionalCompactification P.field
      (Spec (.of P.field.k) ↘ Spec (.of P.field.k))) (integralExceptionalCompactification P.field
      (f ≫ (Spec (.of P.field.k) ↘ Spec (.of P.field.k)))) (.integral
        (AdicPurityScalarNaturality.fieldStage P.field P.coefficients F))),
    let j := AdicPurityScalarNaturality.fieldStage P.field P.coefficients E
    let k := AdicPurityScalarNaturality.fieldStage P.field P.coefficients F
    let QX := AdicPurityScalarNaturality.scalar P.field P.coefficients
      J.scalarClosed E F h true
    let QY := AdicPurityScalarNaturality.scalar P.field P.coefficients
      J.scalarClosed E F h false
    ∃ b : VerdierExchange.StageScalar P.coefficients.l P.coefficients.Qbar
        (p.stage (.integral j)) (p.stage (.integral k)) QX QY QY,
      (b.structureX.q P.coefficients.l P.coefficients.Qbar) = J.c E F h ∧
      (b.structureX.b P.coefficients.l P.coefficients.Qbar) = J.b E F h ∧
      (∀ N, (b.exceptional.q P.coefficients.l P.coefficients.Qbar).hom.app N =
        (AdicPurityScalarNaturality.scalarBridge P.field P.coefficients f Sf
          J.scalarClosed E F h false ((Sf.ring.operation
            (integralExceptionalCompactification P.field f) (.integral j)).F.obj N)).hom ≫
        (AdicPurityScalarNaturality.compactComparison P.field P.coefficients f Sf
          E F h).hom.app N ≫
        (Sf.ring.operation (integralExceptionalCompactification P.field f) (.integral k)).F.map
          (AdicPurityScalarNaturality.scalarBridge P.field P.coefficients f Sf
            J.scalarClosed E F h true N).inv) ∧
    (finiteTorConstructibleIntegral P.coefficients.l F.val
        (Spec (.of P.field.k))).ι.map b.unit.hom ≫
        (p.ring (.integral k)).unitIso.hom =
      (finiteTorConstructibleIntegral P.coefficients.l F.val
        (Spec (.of P.field.k))).ι.map
          (AdicPurityScalarNaturality.scalarBridge P.field P.coefficients f Sf
            J.scalarClosed E F h false (p.unit (.integral j))).hom ≫
        (AdicPurityScalarNaturality.rawScalar P.field P.coefficients f Sf E F h
          false).realization.hom.app (p.unit (.integral j)) ≫
        (pbcDerivedExtend ((PurCompactSupport.completedChange P.coefficients.l
          E.val F.val (IntermediateField.inclusion h)).map (Spec (.of P.field.k)))).map
          (p.ring (.integral j)).unitIso.hom ≫
        VerdierExchange.ringUnitScalar P.coefficients.l
          (s := .integral j) (t := .integral k)
          (PurCompactSupport.completedChange P.coefficients.l E.val F.val
            (IntermediateField.inclusion h)) (Spec (.of P.field.k)) ∧
    let U := p.unit (.integral j)
    let γs := (J.gamma E).app U
    let γt := (J.gamma F).app (p.unit (.integral k))
    let hQ := (J.a E F h).app U ≪≫
      (AdicPurityScalarNaturality.source P.field P.coefficients
        (f ≫ (Spec (.of P.field.k) ↘ Spec (.of P.field.k))) d F).mapIso b.unit
    QX.map γs.hom ≫ (b.kappaX P.coefficients.l P.coefficients.Qbar).hom =
      hQ.hom ≫ γt.hom ∧
    QX.map γs.inv ≫ hQ.hom =
      (b.kappaX P.coefficients.l P.coefficients.Qbar).hom ≫ γt.inv ∧
    smoothOrientationExchangeSquare P.coefficients.l P.coefficients.Qbar
      (p.stage (.integral j)) (p.stage (.integral k)) b
      (p.conclusion (.integral j) hs) (p.conclusion (.integral k) ht) M ∧
    smoothOrientationTransportSquare P.coefficients.l P.coefficients.Qbar
      (p.stage (.integral j)) (p.stage (.integral k)) b _ _ γs γt hQ.hom M

/-- Integral reduction purity, exchange and oriented squares at every positive level.
The support comparison is on the point, the dual maps transpose evaluation, and
orientation uses the inverse of the specified purity component.
Source: latest blueprint, global Verdier duality proof, coefficient passage
(blueprint: def-pod-integral-oriented-exchange-squares). -/
@[irreducible] def smoothIntegralReductionExchangeSquares : Prop :=
  ∀ (J : AdicPurityScalarNaturality.Data P.field P.coefficients
      (f ≫ (Spec (.of P.field.k) ↘ Spec (.of P.field.k))) d SX)
    (E : AdicPurityScalarNaturality.Field P.field P.coefficients) (n : ℕ)
    (M : ConstructibleExceptionalCoefficients.C.{u, u} P.coefficients.l
      P.coefficients.Qbar X (.integral
        (AdicPurityScalarNaturality.fieldStage P.field P.coefficients E)))
    (_hM : IsIntegralCoefficientSitePerfect P.coefficients.l E.val X M.obj)
    (hs : AdmissibleVerdierExchange.admissible P.coefficients.l P.coefficients.Qbar
      P.field P.coefficients.different f
        (integralExceptionalCompactification P.field f)
        (integralExceptionalCompactification P.field
      (Spec (.of P.field.k) ↘ Spec (.of P.field.k))) (integralExceptionalCompactification P.field
      (f ≫ (Spec (.of P.field.k) ↘ Spec (.of P.field.k)))) (.integral
        (AdicPurityScalarNaturality.fieldStage P.field P.coefficients E)))
    (ht : AdmissibleVerdierExchange.admissible P.coefficients.l P.coefficients.Qbar
      P.field P.coefficients.different f
        (integralExceptionalCompactification P.field f)
        (integralExceptionalCompactification P.field
      (Spec (.of P.field.k) ↘ Spec (.of P.field.k))) (integralExceptionalCompactification P.field
      (f ≫ (Spec (.of P.field.k) ↘ Spec (.of P.field.k)))) (.finite
        (AdicPurityScalarNaturality.fieldStage P.field P.coefficients E)
        ⟨n + 1, Nat.succ_pos n⟩)),
    let j := AdicPurityScalarNaturality.fieldStage P.field P.coefficients E
    let r : ℕ+ := ⟨n + 1, Nat.succ_pos n⟩
    let QX := smoothIntegralOrientationReduction P E X n
    let QY := smoothIntegralOrientationReduction P E (Spec (.of P.field.k)) n
    ∃ b : VerdierExchange.StageScalar P.coefficients.l P.coefficients.Qbar
        (p.stage (.integral j)) (p.stage (.finite j r)) QX QY QY,
      smoothOrientationReductionSupportSquare P f Sf
        (integralExceptionalCompactification P.field f) E n
        (b.exceptional.q P.coefficients.l P.coefficients.Qbar) ∧
      smoothOrientationReductionSupportSquare P
        (Spec (.of P.field.k) ↘ Spec (.of P.field.k)) SY
          (integralExceptionalCompactification P.field
      (Spec (.of P.field.k) ↘ Spec (.of P.field.k))) E n
        (b.structureY.q P.coefficients.l P.coefficients.Qbar) ∧
      smoothOrientationReductionSupportSquare P
        (f ≫ (Spec (.of P.field.k) ↘ Spec (.of P.field.k))) SX
          (integralExceptionalCompactification P.field
      (f ≫ (Spec (.of P.field.k) ↘ Spec (.of P.field.k)))) E n
        (b.structureX.q P.coefficients.l P.coefficients.Qbar) ∧
    (finiteTorConstructible P.coefficients.l E.val r r.pos
        (Spec (.of P.field.k))).ι.map b.unit.hom ≫
        (p.ring (.finite j r)).unitIso.hom =
      (AdicPurityScalarNaturality.reductionBridge P.field P.coefficients E
        (Spec (.of P.field.k)) n).hom.app (p.unit (.integral j)).obj ≫
        (pbcDerivedExtend ((PurCompactSupport.reduction P.coefficients.l E.val
          r r.pos).map (Spec (.of P.field.k)))).map
          (p.ring (.integral j)).unitIso.hom ≫
        VerdierExchange.ringUnitScalar P.coefficients.l
          (s := .integral j) (t := .finite j r)
          (PurCompactSupport.reduction P.coefficients.l E.val r r.pos)
          (Spec (.of P.field.k)) ∧
    let U := p.unit (.integral j)
    let γs := (J.gamma E).app U
    let γt₀ := smoothOrientationAtStage P
      (f ≫ (Spec (.of P.field.k) ↘ Spec (.of P.field.k))) d SX
        (integralExceptionalCompactification P.field
      (f ≫ (Spec (.of P.field.k) ↘ Spec (.of P.field.k))))
      (.finite E r) (p.unit (.finite j r))
    let γt := γt₀.2
    let PE := purAdicFiniteSetting P.field P.coefficients E.val n
    let hQ : QX.obj ((AdicPurityScalarNaturality.source P.field P.coefficients
        (f ≫ (Spec (.of P.field.k) ↘ Spec (.of P.field.k))) d E).obj U) ⟶ γt₀.1 :=
      ObjectProperty.homMk (purAdicSourceReduction P.field P.coefficients E.val
        (f ≫ (Spec (.of P.field.k) ↘ Spec (.of P.field.k))) d U.obj U.property n ≫
        (PE.compositionShiftedPullback
          (f ≫ (Spec (.of P.field.k) ↘ Spec (.of P.field.k))) d).map
          ((finiteTorConstructible P.coefficients.l E.val r r.pos
            (Spec (.of P.field.k))).ι.map b.unit.hom))
    QX.map γs.hom ≫ (b.kappaX P.coefficients.l P.coefficients.Qbar).hom =
      hQ ≫ γt.hom ∧
    QX.map γs.inv ≫ hQ =
      (b.kappaX P.coefficients.l P.coefficients.Qbar).hom ≫ γt.inv ∧
    smoothOrientationExchangeSquare P.coefficients.l P.coefficients.Qbar
      (p.stage (.integral j)) (p.stage (.finite j r)) b
      (p.conclusion (.integral j) hs) (p.conclusion (.finite j r) ht) M ∧
    smoothOrientationTransportSquare P.coefficients.l P.coefficients.Qbar
      (p.stage (.integral j)) (p.stage (.finite j r)) b _ _ γs γt hQ M

end CoefficientExchangeTransitions

end WeilConjectures
