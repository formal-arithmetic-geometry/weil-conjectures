/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficientsData
public import WeilConjectures.SmoothPurity.Common.CommonStageInternalHomData
import all WeilConjectures.SixFunctors.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficientStages
import all Mathlib.Logic.Small.Defs
import all Mathlib.Algebra.Field.Shrink
import all Mathlib.Algebra.Algebra.Shrink

/-! # Compactification comparison for a fixed rational operation

Source: the exceptional-adjunction paragraph of the current blueprint,
cor-coef-verdier-weil-equivariance.proof.md.
(blueprint: lem-sf-compact-support-rational-compactification-comparison) -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients
open GeneralAlgebraicallyClosedCoefficients

/-- Independence of compactification, with the morphism and coefficient system fixed.
Source: compactification refinement in the exceptional-adjunction construction;
current blueprint cor-coef-verdier-weil-equivariance.proof.md, final sentence
(blueprint: lem-sf-compact-support-rational-compactification-comparison).

Proof: take the common refinement c inf d. On strict positive quotient systems,
use the normalized open-unit/proper-counit refinement map along its two proper
projections. Proper base change makes these maps invertible on open-supported
constructible objects. Their coefficient squares commute by the scalar mate
normalization: both transposes are the open unit followed by the same coefficient
restriction. Apply completed realization to these actual system maps, retaining
their squares, and localize the inverse of the first followed by the second.
Conjugate by R.rationalLeft and use F.rational_normalized to identify the rational
scalar maps. Whiskering by the recorded stage identifications yields the display.
No target isomorphism or pullback functor appears. When c=d, the identity map
satisfies the square; empty support and zero input give its zero components. -/
theorem compact_support_rational_compactification_comparison
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (R : RingSystem.{u, v} l Ω D hl (f := f))
    (F : FieldSystem.{u, v} l Ω D hl R) (c d : Compactification f) :
    ∃ b : ∀ i : AlgebraicallyClosedCoefficients.Index l Ω,
      (R.operation c (.rational (commonField.{u, v} l Ω i))).F ≅
        (R.operation d (.rational (commonField.{u, v} l Ω i))).F,
      ∀ {i j : AlgebraicallyClosedCoefficients.Index l Ω} (hij : i ≤ j)
        (K : C.{u, v} l Ω X (.rational (commonField.{u, v} l Ω i))),
        ((stageSystem l Ω Y).T hij).map ((b i).hom.app K) ≫
          (Functor.isoWhiskerLeft
              (R.operation d (.rational (commonField.{u, v} l Ω i))).F
              (operationStageTransitionIso l Ω Y i j hij) ≪≫
            (F.rationalComparison d (commonField.{u, v} l Ω i)
              (commonField.{u, v} l Ω j)
              (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j hij)).q ≪≫
            Functor.isoWhiskerRight
              (operationStageTransitionIso l Ω X i j hij).symm
              (R.operation d (.rational (commonField.{u, v} l Ω j))).F).hom.app K =
          (Functor.isoWhiskerLeft
              (R.operation c (.rational (commonField.{u, v} l Ω i))).F
              (operationStageTransitionIso l Ω Y i j hij) ≪≫
            (F.rationalComparison c (commonField.{u, v} l Ω i)
              (commonField.{u, v} l Ω j)
              (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω i j hij)).q ≪≫
            Functor.isoWhiskerRight
              (operationStageTransitionIso l Ω X i j hij).symm
              (R.operation c (.rational (commonField.{u, v} l Ω j))).F).hom.app K ≫
            (b j).hom.app (((stageSystem l Ω X).T hij).obj K) := by
  sorry

end WeilConjectures.ConstructibleExceptionalCoefficients
