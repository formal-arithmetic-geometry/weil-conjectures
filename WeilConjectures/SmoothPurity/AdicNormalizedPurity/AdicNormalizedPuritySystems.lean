/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.SmoothPurityMap
public import WeilConjectures.SmoothPurity.Adic.AdicPuritySourceReduction
public import WeilConjectures.SmoothPurity.Adic.AdicPurityExceptionalReduction
public import WeilConjectures.SmoothPurity.Adic.AdicPuritySourceFiniteness
public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRTower
public import WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerCanonical
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionRootCharts
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionComparisons
public import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorComparison
public import WeilConjectures.SmoothPurity.Integral.IntegralExceptionalInverseImage
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Composition.PurityCompositionCoherence
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement

/-! # Canonical systems and evaluation maps for normalized finite purity

Source: blueprint, sec-smooth-purity/sk-thm-purity-transport, integral reconstruction;
current transport proof Step 1 and det-sp-tower-gamma, referenced by the coefficient-change
proof. (blueprint: def-pur-adic-normalized-purity-systems).

The source is the strict reduction of Lf* K(d)[2d]. The target is the actual exceptional
coefficient system before its derived limit. All evaluation maps and quotient comparisons
below are composites of the recorded canonical maps. Natural number n means exponent n+1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.AdicNormalizedPurity

variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
  (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (d : ℕ) [SmoothOfRelativeDimension d f]

/-- The actual coherent reduction of U, retaining quotient coefficient actions.
Source: reconstruction proof, normalized source system
(blueprint: def-pur-adic-normalized-purity-systems). -/
def sourceSequence (K : DerivedCategory (scalarReductionSource C.l E Y)) :=
  (pullbackTensorCalculus C.l E X).reduction.obj (purAdicSource D C E f d K)

/-- The actual exceptional coefficient system whose total limit defines Rf! K.
Source: reconstruction proof, actual exceptional system
(blueprint: def-pur-adic-normalized-purity-systems). -/
def targetSequence (K : DerivedCategory (scalarReductionSource C.l E Y)) :=
  (integralExceptionalSystem C.l E D C.different f).obj K

/-- Forget the source's varying coefficient actions to the completed ring.
Source: reconstruction proof, restriction to R_X
(blueprint: def-pur-adic-normalized-purity-systems). -/
def sourceTower (K : DerivedCategory (scalarReductionSource C.l E Y)) :=
  (coefficientSequenceDerivedRestriction C.l E X).obj (sourceSequence D C E f d K)

/-- Forget the actual exceptional system's coefficient actions to the completed ring.
Source: reconstruction proof, restriction to R_X
(blueprint: def-pur-adic-normalized-purity-systems). -/
def targetTower (K : DerivedCategory (scalarReductionSource C.l E Y)) :=
  (coefficientSequenceDerivedRestriction C.l E X).obj (targetSequence D C E f K)

/-- Source evaluation is the specified reduction evaluation followed by b^U_n.
Source: reconstruction proof, source identifications
(blueprint: def-pur-adic-normalized-purity-systems). -/
@[no_expose] def sourceEvaluation
    (K : DerivedCategory (scalarReductionSource C.l E Y))
    (hK : finiteTorConstructibleIntegral C.l E Y K) (n : ℕ) :
    (normalizedDVRTowerEvaluation C.l E X D C.different n).obj
        (sourceTower D C E f d K) ⟶
      (normalizedDVRResCompleted C.l E X D C.different n).obj
        (purAdicFiniteArrow D C E f d K hK n).left :=
  (coefficientRestrictedEvaluationIso C.l E X n).hom.app _ ≫
    (normalizedDVRResCompleted C.l E X D C.different n).map
      (((pullbackTensorCalculus C.l E X).reductionEvaluation n).hom.app _ ≫
        purAdicSourceReduction D C E f d K hK n)

/-- Target evaluation is the normalized coordinate/site/compact-support mate comparison.
Source: reconstruction proof, exceptional evaluations
(blueprint: def-pur-adic-normalized-purity-systems). -/
@[no_expose] def targetEvaluation
    (K : DerivedCategory (scalarReductionSource C.l E Y))
    (hK : finiteTorConstructibleIntegral C.l E Y K) (n : ℕ) :
    (normalizedDVRTowerEvaluation C.l E X D C.different n).obj
        (targetTower D C E f K) ≅
      (normalizedDVRResCompleted C.l E X D C.different n).obj
        (purAdicFiniteArrow D C E f d K hK n).right :=
  (coefficientRestrictedEvaluationIso C.l E X n).app _ ≪≫
    (normalizedDVRResCompleted C.l E X D C.different n).mapIso
      (purAdicExceptionalEvaluation D C E f K n)

/-- rho^V is finite exceptional coefficient comparison followed by Rf_n! of the
actual input normalization. It is defined independently of the purity maps.
Source: reconstruction proof, identification of exceptional normalization
(blueprint: def-pur-adic-normalized-purity-systems). -/
@[no_expose] def exceptionalNormalization
    (K : DerivedCategory (scalarReductionSource C.l E Y))
    (hK : finiteTorConstructibleIntegral C.l E Y K) {m n : ℕ} (h : n ≤ m) :
    ((purAdicFiniteSetting D C E m).finiteReduction (n + 1) (Nat.succ_pos n)
      (Nat.add_le_add_right h 1) X).obj
        (purAdicFiniteArrow D C E f d K hK m).right ⟶
      (purAdicFiniteArrow D C E f d K hK n).right :=
  (purAdicFiniteSetting D C E m).finiteReductionExceptionalComparison (n + 1)
      (Nat.succ_pos n) (Nat.add_le_add_right h 1) f d
      ((scalarReductionDerivedExtension C.l E Y m).obj K)
      (purAdicReductionFiniteTor D C E Y K hK m) ≫
    ((purAdicFiniteSetting D C E n).compositionExceptional f).map
      (purAdicQuotientNormalization D C E Y h K)

/-- Transport the actual exceptional-system transition by its canonical evaluations.
Its agreement with the transpose of rho^V is asserted in normalized_purity_lift.
Source: reconstruction proof, actual exceptional transition mates
(blueprint: def-pur-adic-normalized-purity-systems). -/
@[no_expose] def exceptionalTransition
    (K : DerivedCategory (scalarReductionSource C.l E Y))
    (hK : finiteTorConstructibleIntegral C.l E Y K) {m n : ℕ} (h : n ≤ m) :
    (purAdicFiniteArrow D C E f d K hK m).right ⟶
      (normalizedDVRRes C.l E X h).obj (purAdicFiniteArrow D C E f d K hK n).right :=
  (purAdicExceptionalEvaluation D C E f K m).inv ≫
    (coefficientSequenceDerivedTransition C.l E X h).app (targetSequence D C E f K) ≫
    (normalizedDVRRes C.l E X h).map (purAdicExceptionalEvaluation D C E f K n).hom

/-- The source transition after restriction to the completed coefficient ring.
Source: reconstruction proof, displayed successive-transition equation
(blueprint: def-pur-adic-normalized-purity-systems). -/
@[no_expose] def sourceRestrictedTransition
    (K : DerivedCategory (scalarReductionSource C.l E Y))
    (hK : finiteTorConstructibleIntegral C.l E Y K) {m n : ℕ} (h : n ≤ m) :=
  (normalizedDVRResCompleted C.l E X D C.different m).map
      (purAdicFiniteSourceTransition D C E f d K hK h) ≫
    (normalizedDVRResCompletedComp C.l E X D C.different h).hom.app _

/-- The exceptional transition after restriction to the completed coefficient ring.
Source: reconstruction proof, displayed successive-transition equation
(blueprint: def-pur-adic-normalized-purity-systems). -/
@[no_expose] def targetRestrictedTransition
    (K : DerivedCategory (scalarReductionSource C.l E Y))
    (hK : finiteTorConstructibleIntegral C.l E Y K) {m n : ℕ} (h : n ≤ m) :=
  (normalizedDVRResCompleted C.l E X D C.different m).map
      (exceptionalTransition D C E f d K hK h) ≫
    (normalizedDVRResCompletedComp C.l E X D C.different h).hom.app _

end WeilConjectures.AdicNormalizedPurity
