/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothOrientationCoefficientFamily
public import WeilConjectures.AlgebraicGeometry.SmoothOrientationTransportSquare
public import WeilConjectures.AlgebraicGeometry.AdmissibleVerdierExchange
public import WeilConjectures.AlgebraicGeometry.RationalizationOrientedExchangeSquare
import all WeilConjectures.AlgebraicGeometry.AdicPurityScalarNaturalityData

/-! # Site exchange comparisons under the smooth orientation

Source: latest blueprint, sec-six-functors/sk-thm-sf-package,
thm-pod-global-verdier-duality.proof.md, second paragraph
(blueprint: def-pod-field-oriented-exchange-squares).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
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
  RationalSmoothPurityCanonical.integralSource
  RationalSmoothPurityCanonical.rationalSourceComparison
  RationalSmoothPurityCanonical.smallModelIso
  RationalSmoothPurityCanonical.commonIso
  RationalSmoothPurityCanonical.commonSourceComparison
  RationalSmoothPurityCanonical.sourceScalar
  RationalSmoothPurityCanonical.rationalSource
  RationalSmoothPurityCanonical.commonSource
  smoothOrientationAtStage

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

set_option maxHeartbeats 300000 in
-- The three normalized common-stage operation types require explicit size transports.
/-- Common finite-stage purity, exchange and oriented squares.
The support comparison is on the point, the dual maps transpose evaluation, and
orientation uses the inverse of the specified purity component.
Source: latest blueprint, global Verdier duality proof, coefficient passage
(blueprint: def-pod-field-oriented-exchange-squares). -/
@[irreducible] def smoothCommonStageExchangeSquares : Prop :=
  ∀ (i : AlgebraicallyClosedCoefficients.Index P.coefficients.l P.coefficients.Qbar)
    (M : ConstructibleExceptionalCoefficients.C.{u, u} P.coefficients.l
      P.coefficients.Qbar X (.rational
        (ConstructibleExceptionalCoefficients.commonField P.coefficients.l
          P.coefficients.Qbar i)))
    (_hM : smoothOrientationSitePerfect P.coefficients.l P.coefficients.Qbar X
      (.rational (ConstructibleExceptionalCoefficients.commonField P.coefficients.l
        P.coefficients.Qbar i)) M)
    (hs : AdmissibleVerdierExchange.admissible P.coefficients.l P.coefficients.Qbar
      P.field P.coefficients.different f
        (integralExceptionalCompactification P.field f)
        (integralExceptionalCompactification P.field
      (Spec (.of P.field.k) ↘ Spec (.of P.field.k))) (integralExceptionalCompactification P.field
      (f ≫ (Spec (.of P.field.k) ↘ Spec (.of P.field.k)))) (.rational
        (ConstructibleExceptionalCoefficients.commonField P.coefficients.l
          P.coefficients.Qbar i)))
    (ht : AdmissibleVerdierExchange.admissible P.coefficients.l P.coefficients.Qbar
      P.field P.coefficients.different f
        (integralExceptionalCompactification P.field f)
        (integralExceptionalCompactification P.field
      (Spec (.of P.field.k) ↘ Spec (.of P.field.k))) (integralExceptionalCompactification P.field
      (f ≫ (Spec (.of P.field.k) ↘ Spec (.of P.field.k)))) .closed),
    let j := ConstructibleExceptionalCoefficients.commonField P.coefficients.l
      P.coefficients.Qbar i
    let QX := ConstructibleExceptionalCoefficients.commonInclusion P.coefficients.l
      P.coefficients.Qbar X i
    let QY := ConstructibleExceptionalCoefficients.commonInclusion P.coefficients.l
      P.coefficients.Qbar (Spec (.of P.field.k)) i
    ∃ b : VerdierExchange.StageScalar P.coefficients.l P.coefficients.Qbar
        (p.stage (.rational j)) (p.stage .closed) QX QY QY,
      b.exceptional = Sf.common.commonComparison (integralExceptionalCompactification P.field f) i ∧
      b.structureY = SY.common.commonComparison (integralExceptionalCompactification P.field
      (Spec (.of P.field.k) ↘ Spec (.of P.field.k))) i ∧
      b.structureX = SX.common.commonComparison (integralExceptionalCompactification P.field
      (f ≫ (Spec (.of P.field.k) ↘ Spec (.of P.field.k)))) i ∧
    let γs := RationalSmoothPurityCanonical.smallModelIso
      (RationalSmoothPurityCanonical.stageSetting P i)
      (f ≫ (Spec (.of P.field.k) ↘ Spec (.of P.field.k)))
        (integralExceptionalCompactification P.field
      (f ≫ (Spec (.of P.field.k) ↘ Spec (.of P.field.k)))) SX d
      (p.unit (.rational j))
    let γt := RationalSmoothPurityCanonical.commonIso P
      (f ≫ (Spec (.of P.field.k) ↘ Spec (.of P.field.k)))
        (integralExceptionalCompactification P.field
      (f ≫ (Spec (.of P.field.k) ↘ Spec (.of P.field.k)))) SX d
      (p.unit .closed)
    let hQ := (RationalSmoothPurityCanonical.commonSourceComparison P.coefficients.l
      P.coefficients.Qbar
      (f ≫ (Spec (.of P.field.k) ↘ Spec (.of P.field.k))) d
      (QY.obj (p.unit (.rational j)))).symm ≪≫
      (RationalSmoothPurityCanonical.commonSource P.coefficients.l P.coefficients.Qbar
        (f ≫ (Spec (.of P.field.k) ↘ Spec (.of P.field.k))) d).mapIso b.unit
    smoothOrientationPuritySquare QX γs γt hQ
      (b.kappaX P.coefficients.l P.coefficients.Qbar) ∧
    smoothOrientationExchangeSquare P.coefficients.l P.coefficients.Qbar
      (p.stage (.rational j)) (p.stage .closed) b
      (p.conclusion (.rational j) hs) (p.conclusion .closed ht) M ∧
    smoothOrientationTransportSquare P.coefficients.l P.coefficients.Qbar
      (p.stage (.rational j)) (p.stage .closed) b _ _ γs γt hQ.hom M

/-- Rational field-extension purity, exchange and oriented squares.
The support comparison is on the point, the dual maps transpose evaluation, and
orientation uses the inverse of the specified purity component.
Source: latest blueprint, global Verdier duality proof, coefficient passage
(blueprint: def-pod-field-oriented-exchange-squares). -/
@[irreducible] def smoothRationalScalarExchangeSquares
    (E : AdicPurityScalarNaturality.Field P.field P.coefficients)
    (K : ConstructibleExceptionalCoefficients.C.{u, u} P.coefficients.l P.coefficients.Qbar X
      (.rational (AdicPurityScalarNaturality.fieldStage P.field P.coefficients E))) : Prop :=
  let E₀ := AdicPurityScalarNaturality.fieldStage P.field P.coefficients E
  ∀ (F : AdicPurityScalarNaturality.Field P.field P.coefficients)
    (h : E ≤ F)
    (hs : AdmissibleVerdierExchange.admissible P.coefficients.l P.coefficients.Qbar
      P.field P.coefficients.different f
        (integralExceptionalCompactification P.field f)
        (integralExceptionalCompactification P.field
      (Spec (.of P.field.k) ↘ Spec (.of P.field.k))) (integralExceptionalCompactification P.field
      (f ≫ (Spec (.of P.field.k) ↘ Spec (.of P.field.k)))) (.rational E₀))
    (ht : AdmissibleVerdierExchange.admissible P.coefficients.l P.coefficients.Qbar
      P.field P.coefficients.different f
        (integralExceptionalCompactification P.field f)
        (integralExceptionalCompactification P.field
      (Spec (.of P.field.k) ↘ Spec (.of P.field.k))) (integralExceptionalCompactification P.field
      (f ≫ (Spec (.of P.field.k) ↘ Spec (.of P.field.k)))) (.rational
        (AdicPurityScalarNaturality.fieldStage P.field P.coefficients F))),
  let i := IntermediateField.inclusion h
  let fE := AdicPurityScalarNaturality.fieldStage P.field P.coefficients F
  let QX := ConstructibleExceptionalCoefficients.rationalScalar P.coefficients.l
    P.coefficients.Qbar E₀ fE i X
  let QY := ConstructibleExceptionalCoefficients.rationalScalar P.coefficients.l
    P.coefficients.Qbar E₀ fE i (Spec (.of P.field.k))
  ∃ b : VerdierExchange.StageScalar P.coefficients.l P.coefficients.Qbar
      (p.stage (.rational E₀)) (p.stage (.rational fE)) QX QY QY,
    b.exceptional = Sf.fields.rationalComparison
      (integralExceptionalCompactification P.field f) E₀ fE i ∧
    b.structureY = SY.fields.rationalComparison (integralExceptionalCompactification P.field
      (Spec (.of P.field.k) ↘ Spec (.of P.field.k))) E₀ fE i ∧
    b.structureX = SX.fields.rationalComparison (integralExceptionalCompactification P.field
      (f ≫ (Spec (.of P.field.k) ↘ Spec (.of P.field.k)))) E₀ fE i ∧
  let γs := smoothOrientationAtStage P
    (f ≫ (Spec (.of P.field.k) ↘ Spec (.of P.field.k))) d SX
      (integralExceptionalCompactification P.field
      (f ≫ (Spec (.of P.field.k) ↘ Spec (.of P.field.k))))
    (.rational E) (p.unit (.rational E₀))
  let γt := smoothOrientationAtStage P
    (f ≫ (Spec (.of P.field.k) ↘ Spec (.of P.field.k))) d SX
      (integralExceptionalCompactification P.field
      (f ≫ (Spec (.of P.field.k) ↘ Spec (.of P.field.k))))
    (.rational F) (p.unit (.rational fE))
  let hQ := smoothRationalOrientationSourceComparison P
    (f ≫ (Spec (.of P.field.k) ↘ Spec (.of P.field.k))) d SX
      (integralExceptionalCompactification P.field
      (f ≫ (Spec (.of P.field.k) ↘ Spec (.of P.field.k)))) E F i
    (p.unit (.rational E₀)) (p.unit (.rational fE)) b.unit
  smoothOrientationPuritySquare QX γs.2 γt.2 hQ
    (b.kappaX P.coefficients.l P.coefficients.Qbar) ∧
  smoothOrientationExchangeSquare P.coefficients.l P.coefficients.Qbar
    (p.stage (.rational E₀)) (p.stage (.rational fE)) b
    (p.conclusion (.rational E₀) hs) (p.conclusion (.rational fE) ht) K ∧
  smoothOrientationTransportSquare P.coefficients.l P.coefficients.Qbar
    (p.stage (.rational E₀)) (p.stage (.rational fE)) b γs.1 γt.1 γs.2 γt.2 hQ.hom K

end CoefficientExchangeTransitions

end WeilConjectures
