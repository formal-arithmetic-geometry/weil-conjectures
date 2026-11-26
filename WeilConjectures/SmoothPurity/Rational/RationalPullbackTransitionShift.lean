/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Common.CommonStagePullbackNormalizedDescent
public import WeilConjectures.FourierTransform.IntegralCompletedComparison.IntegralPullbackShiftCoordinates
import WeilConjectures.SmoothPurity.Rational.RationalPullbackTransitionShiftScalar
import WeilConjectures.SmoothPurity.Rational.RationalPullbackTransitionShiftRational
import WeilConjectures.CategoryTheory.Shift.CommShiftEqToIso

/-! # Scalar compatibility of normalized pullback shifts

The proof is split into the following steps:
- `WeilConjectures.SmoothPurity.Rational.RationalPullbackTransitionShiftRoos`: the Roos
  scalar/tower chain comparison commutes with signed Roos shifts;
- `WeilConjectures.SmoothPurity.Rational.RationalPullbackTransitionShiftLevel`: the
  finite scalar pullback levels commute with shifts;
- `WeilConjectures.SmoothPurity.Rational.RationalPullbackTransitionShiftIntegral`: the
  ordinary scalar/pullback comparison commutes with shifts;
- `WeilConjectures.SmoothPurity.Rational.RationalPullbackTransitionShiftScalar`: the
  integral pullback scalar comparison commutes with shifts;
- `WeilConjectures.SmoothPurity.Rational.RationalPullbackTransitionShiftRational`: the
  rational pullback scalar comparison commutes with shifts.

## Implementation details

The coordinates are the signed Roos coordinates, fixed on every good representative by the
descent comparisons, and the coefficient transition uses the canonical completed scalar shifts
normalized by `integralTransitionCommShift`. The framework theta theorem applies to these four
shifts, using any finite-field datum of characteristic different from `l`. Theta is identified
with the integral pullback scalar comparison, and rational localization together with the
degree-one formulas gives the rational square at one; the `CommShift` laws extend it to all
integers. Finally `commonStagePullbackTransition` conjugates this comparison by the recorded
stage-transition isomorphisms, which preserve the transported shifts.
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
universe u v
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
attribute [local irreducible] constructibleIntegralPullback rationalDerivedPullback
  rationalPullbackScalarComparison

set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.Stage
  GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.stageShift
set_option linter.auxLemma false in
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_1
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_3
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_5
attribute [local instance 5000] GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.stageShift

/-- The actual coefficient-transition comparison preserves normalized pullback shifts. -/
theorem rationalPullbackTransitionShift
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (E L : Index l Ω) (h : E ≤ L)
    [sE : (constructibleIntegralPullback l (Coefficient.{u} l Ω E) f).CommShift ℤ]
    [sL : (constructibleIntegralPullback l (Coefficient.{u} l Ω L) f).CommShift ℤ]
    [rE : (rationalDerivedPullback l (Coefficient.{u} l Ω E) f).CommShift ℤ]
    [rL : (rationalDerivedPullback l (Coefficient.{u} l Ω L) f).CommShift ℤ]
    (hE : ∃ (c : (integralOperationsPullbackComplexFunctor l
          (Coefficient.{u} l Ω E) f).CommShift ℤ)
        (d : (integralDerivedPullback l (Coefficient.{u} l Ω E) f).CommShift ℤ),
      IntegralCompletedComparison.ShiftCoordinates l (Coefficient.{u} l Ω E) f c ∧
      IntegralCompletedComparison.ShiftDescent l (Coefficient.{u} l Ω E) f c d ∧
      ∀ (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) X) (n : ℤ),
        HEq (((constructibleIntegralPullback l (Coefficient.{u} l Ω E) f).commShiftIso
          n).hom.app K).hom
          (((integralDerivedPullback l (Coefficient.{u} l Ω E) f).commShiftIso
            (self := d) n).hom.app K.obj))
    (hL : ∃ (c : (integralOperationsPullbackComplexFunctor l
          (Coefficient.{u} l Ω L) f).CommShift ℤ)
        (d : (integralDerivedPullback l (Coefficient.{u} l Ω L) f).CommShift ℤ),
      IntegralCompletedComparison.ShiftCoordinates l (Coefficient.{u} l Ω L) f c ∧
      IntegralCompletedComparison.ShiftDescent l (Coefficient.{u} l Ω L) f c d ∧
      ∀ (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω L) X) (n : ℤ),
        HEq (((constructibleIntegralPullback l (Coefficient.{u} l Ω L) f).commShiftIso
          n).hom.app K).hom
          (((integralDerivedPullback l (Coefficient.{u} l Ω L) f).commShiftIso
            (self := d) n).hom.app K.obj))
    (nE : ∀ K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) X,
      HEq (((rationalDerivedPullback l (Coefficient.{u} l Ω E) f).commShiftIso
        (1 : ℤ)).hom.app K)
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) Y).map
          (((constructibleIntegralPullback l (Coefficient.{u} l Ω E) f).commShiftIso
            (1 : ℤ)).hom.app K.obj)))
    (nL : ∀ K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω L) X,
      HEq (((rationalDerivedPullback l (Coefficient.{u} l Ω L) f).commShiftIso
        (1 : ℤ)).hom.app K)
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω L) Y).map
          (((constructibleIntegralPullback l (Coefficient.{u} l Ω L) f).commShiftIso
            (1 : ℤ)).hom.app K.obj))) :
    letI := GeneralAlgebraicallyClosedCoefficients.stageTransitionCommShift l Ω X E L h
    letI := GeneralAlgebraicallyClosedCoefficients.stageTransitionCommShift l Ω Y E L h
    @NatTrans.CommShift _ _ _ _ _ _ (commonStagePullbackTransition l Ω f h).hom ℤ _ _ _
      (@Functor.CommShift.comp _ _ _ _ _ _
        (rationalDerivedPullback l (Coefficient.{u} l Ω E) f)
        ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Y).T h)
        ℤ _ _ _ _ rE
        (GeneralAlgebraicallyClosedCoefficients.stageTransitionCommShift l Ω Y E L h))
      (@Functor.CommShift.comp _ _ _ _ _ _
        ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).T h)
        (rationalDerivedPullback l (Coefficient.{u} l Ω L) f)
        ℤ _ _ _ _
        (GeneralAlgebraicallyClosedCoefficients.stageTransitionCommShift l Ω X E L h)
        rL) := by
  obtain ⟨α, hα, hs⟩ := integralPullbackScalarComparison_commShift l Ω f E L h hE hL
  let := GeneralAlgebraicallyClosedCoefficients.stageTransitionCommShift l Ω X E L h
  let := GeneralAlgebraicallyClosedCoefficients.stageTransitionCommShift l Ω Y E L h
  let := GeneralAlgebraicallyClosedCoefficients.transitionCommShift l Ω X E L h
  let := GeneralAlgebraicallyClosedCoefficients.transitionCommShift l Ω Y E L h
  let β : rationalDerivedPullback l (Coefficient.{u} l Ω E) f ⋙
        GeneralAlgebraicallyClosedCoefficients.transition l Ω Y E L h ⟶
      GeneralAlgebraicallyClosedCoefficients.transition l Ω X E L h ⋙
        rationalDerivedPullback l (Coefficient.{u} l Ω L) f :=
    (rationalPullbackScalarComparison l (Coefficient.{u} l Ω E)
      (Coefficient.{u} l Ω L) (coefficientInclusion l Ω E L h) f).hom
  have hβ : NatTrans.CommShift β ℤ :=
    rationalPullbackScalarComparison_commShift
      (iX := GeneralAlgebraicallyClosedCoefficients.integralTransitionCommShift l Ω X E L h)
      (iY := GeneralAlgebraicallyClosedCoefficients.integralTransitionCommShift l Ω Y E L h)
      (tX := GeneralAlgebraicallyClosedCoefficients.transitionCommShift l Ω X E L h)
      (tY := GeneralAlgebraicallyClosedCoefficients.transitionCommShift l Ω Y E L h)
      l Ω f E L h
      (GeneralAlgebraicallyClosedCoefficients.transitionCommShift_existsUnique
        l Ω X E L h).exists.choose_spec
      (GeneralAlgebraicallyClosedCoefficients.transitionCommShift_existsUnique
        l Ω Y E L h).exists.choose_spec
      nE nL α hα hs
  have htX : NatTrans.CommShift (operationStageTransitionIso l Ω X E L h).hom ℤ :=
    NatTrans.CommShift.eqToIso_hom
      ((GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique
        l Ω X).exists.choose_spec.1 E L h)
      (GeneralAlgebraicallyClosedCoefficients.transitionCommShift l Ω X E L h)
  have htY : NatTrans.CommShift (operationStageTransitionIso l Ω Y E L h).hom ℤ :=
    NatTrans.CommShift.eqToIso_hom
      ((GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique
        l Ω Y).exists.choose_spec.1 E L h)
      (GeneralAlgebraicallyClosedCoefficients.transitionCommShift l Ω Y E L h)
  have key : NatTrans.CommShift
      (Functor.whiskerLeft (rationalDerivedPullback l (Coefficient.{u} l Ω E) f)
          (operationStageTransitionIso l Ω Y E L h).hom ≫ β ≫
        Functor.whiskerRight (operationStageTransitionIso l Ω X E L h).inv
          (rationalDerivedPullback l (Coefficient.{u} l Ω L) f)) ℤ := inferInstance
  exact key

end WeilConjectures
