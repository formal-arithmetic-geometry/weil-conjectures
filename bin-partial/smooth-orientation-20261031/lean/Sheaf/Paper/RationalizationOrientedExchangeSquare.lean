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
(blueprint: def-pod-rationalization-oriented-exchange-square).
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

set_option maxHeartbeats 1000000 in
-- Elaborate the three normalized operation comparisons and both canonical purity maps.
/-- Rationalization with the canonical integral and rational purity maps.
The support comparison is on the point, the dual maps transpose evaluation, and
orientation uses the inverse of the specified purity component.
Source: latest blueprint, global Verdier duality proof, coefficient passage
(blueprint: def-pod-rationalization-oriented-exchange-square). -/
@[irreducible] def smoothRationalizationExchangeSquares
    (E : AdicPurityScalarNaturality.Field P.field P.coefficients)
    (K : ConstructibleExceptionalCoefficients.C.{u, u} P.coefficients.l P.coefficients.Qbar X
      (.integral (AdicPurityScalarNaturality.fieldStage P.field P.coefficients E))) : Prop :=
  let E₀ := AdicPurityScalarNaturality.fieldStage P.field P.coefficients E
  ∀ (hs : AdmissibleVerdierExchange.admissible P.coefficients.l P.coefficients.Qbar
      P.field P.coefficients.different f
        (integralExceptionalCompactification P.field f)
        (integralExceptionalCompactification P.field
      (Spec (.of P.field.k) ↘ Spec (.of P.field.k))) (integralExceptionalCompactification P.field
      (f ≫ (Spec (.of P.field.k) ↘ Spec (.of P.field.k)))) (.integral E₀))
    (ht : AdmissibleVerdierExchange.admissible P.coefficients.l P.coefficients.Qbar
      P.field P.coefficients.different f
        (integralExceptionalCompactification P.field f)
        (integralExceptionalCompactification P.field
      (Spec (.of P.field.k) ↘ Spec (.of P.field.k))) (integralExceptionalCompactification P.field
      (f ≫ (Spec (.of P.field.k) ↘ Spec (.of P.field.k)))) (.rational E₀)),
  let QX := ConstructibleExceptionalCoefficients.rationalization P.coefficients.l
    P.coefficients.Qbar E₀ X
  let QY := ConstructibleExceptionalCoefficients.rationalization P.coefficients.l
    P.coefficients.Qbar E₀ (Spec (.of P.field.k))
  ∃ b : VerdierExchange.StageScalar P.coefficients.l P.coefficients.Qbar
      (p.stage (.integral E₀)) (p.stage (.rational E₀)) QX QY QY,
    b.exceptional = Sf.fields.rationalizationComparison
      (integralExceptionalCompactification P.field f) E₀ ∧
    b.structureY = SY.fields.rationalizationComparison (integralExceptionalCompactification P.field
      (Spec (.of P.field.k) ↘ Spec (.of P.field.k))) E₀ ∧
    b.structureX = SX.fields.rationalizationComparison (integralExceptionalCompactification P.field
      (f ≫ (Spec (.of P.field.k) ↘ Spec (.of P.field.k)))) E₀ ∧
  let PE := RationalSmoothPurityCanonical.stageSetting P E
  let aX := (f ≫ (Spec (.of P.field.k) ↘ Spec (.of P.field.k)))
  let cX := integralExceptionalCompactification P.field aX
  let U := p.unit (.integral E₀)
  let Hs : ConstructibleExceptionalCoefficients.C.{u, u} P.coefficients.l
      P.coefficients.Qbar X (.integral E₀) :=
    RationalSmoothPurityCanonical.integralSource PE aX d U
  let Ht : ConstructibleExceptionalCoefficients.C.{u, u} P.coefficients.l
      P.coefficients.Qbar X (.rational E₀) :=
    (RationalSmoothPurityCanonical.rationalSource P.coefficients.l E.val aX d).obj
      (p.unit (.rational E₀))
  let γs : Hs ≅ (SX.ring.operation cX (.integral E₀)).G.obj U :=
    RationalSmoothPurityCanonical.integralIso PE aX cX SX d U
  let γt : Ht ≅ (SX.ring.operation cX (.rational E₀)).G.obj (p.unit (.rational E₀)) :=
    RationalSmoothPurityCanonical.rationalIso PE aX cX SX d (p.unit (.rational E₀))
  let hQ : QX.obj Hs ≅ Ht :=
    (RationalSmoothPurityCanonical.rationalSourceComparison PE aX d (QY.obj U)).symm ≪≫
      (RationalSmoothPurityCanonical.rationalSource P.coefficients.l E.val aX d).mapIso b.unit
  smoothOrientationPuritySquare QX γs γt hQ
    (b.kappaX P.coefficients.l P.coefficients.Qbar) ∧
  smoothOrientationExchangeSquare P.coefficients.l P.coefficients.Qbar
    (p.stage (.integral E₀)) (p.stage (.rational E₀)) b
    (p.conclusion (.integral E₀) hs) (p.conclusion (.rational E₀) ht) K ∧
  smoothOrientationTransportSquare P.coefficients.l P.coefficients.Qbar
    (p.stage (.integral E₀)) (p.stage (.rational E₀)) b Hs Ht γs γt hQ.hom K

end CoefficientExchangeTransitions

end WeilConjectures
