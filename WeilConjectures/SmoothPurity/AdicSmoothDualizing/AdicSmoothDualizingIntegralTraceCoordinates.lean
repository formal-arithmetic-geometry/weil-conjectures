/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.AdicSmoothDualizing.AdicSmoothDualizingIntegralData
public import WeilConjectures.SmoothPurity.PurUnitTrace.AdicUnitTraceReductionData

/-! # Root normalization of reconstructed integral purity

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-cor-sp-all-coefficients/cor-pur-adic-and-rational-smooth-dualizing-complexes.proof.md.
(blueprint: def-pur-adic-smooth-dualizing-integral-trace-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicSmoothDualizing

variable (P : PurityFiniteSetting.{u}) (X : Scheme.{u})
  [X.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  (S : ConstructibleExceptionalCoefficients.System P.coefficients.l P.coefficients.Qbar
    P.field P.coefficients.different (f := X ↘ Spec (.of P.field.k)))

/-- Pullback of the shifted-zero completed unit, followed by the existing
normalized unit comparison and the tensor unitor.
Source: smooth-dualizing corollary, application at the coefficient unit
(blueprint: def-pur-adic-smooth-dualizing-integral-trace-coordinates). -/
def integralUnitSourceComparison
    (d : ℕ) [SmoothOfRelativeDimension d (X ↘ Spec (.of P.field.k))]
    (core : CompletedUnitPullback.Core P.coefficients.l P.extension
      (X ↘ Spec (.of P.field.k))) :
    purAdicSource P.field P.coefficients P.extension (X ↘ Spec (.of P.field.k)) d
        (integralTwist P (Spec (.of P.field.k)) (𝟙 _) 0).obj ≅
      (integralTwist P X (X ↘ Spec (.of P.field.k)) d).obj :=
  (PurUnitTrace.sourceFunctor P.field P.coefficients P.extension
      (X ↘ Spec (.of P.field.k)) d).mapIso ((shiftFunctorZero _ ℤ).app _) ≪≫
    PurUnitTrace.sourceUnitIso P.field P.coefficients P.extension
      (X ↘ Spec (.of P.field.k)) d core

/-- The finite coefficient-valued trace written in the completed line coordinates.
Every factor is a published coefficient, compact-support or source reduction map.
Source: corollary proof, finite coefficient-unit counit calculation
(blueprint: def-pur-adic-smooth-dualizing-integral-trace-coordinates). -/
@[irreducible]
def integralFiniteTrace (d : ℕ)
    [SmoothOfRelativeDimension d (X ↘ Spec (.of P.field.k))]
    (core : CompletedUnitPullback.Core P.coefficients.l P.extension
      (X ↘ Spec (.of P.field.k))) (n : ℕ) :
    (pbcDerivedExtend (PurCompactSupport.projection P.coefficients.l P.extension
        (n + 1) (Nat.succ_pos n) (Spec (.of P.field.k)))).obj
      ((PurCompactSupport.image (PurCompactSupport.completed P.coefficients.l P.extension)
        (compactification P X)).obj (integralTwist P X (X ↘ Spec (.of P.field.k)) d).obj) ⟶
      (pbcDerivedExtend (PurCompactSupport.projection P.coefficients.l P.extension
        (n + 1) (Nat.succ_pos n) (Spec (.of P.field.k)))).obj
          (integralTwist P (Spec (.of P.field.k)) (𝟙 _) 0).obj :=
  (PurCompactSupport.comparison (PurCompactSupport.reduction P.coefficients.l P.extension
      (n + 1) (Nat.succ_pos n)) (compactification P X)).app _ ≫
    (PurCompactSupport.image (PurCompactSupport.finite P.coefficients.l P.extension
      (n + 1) (Nat.succ_pos n)) (compactification P X)).map
        ((PurCompactSupport.finiteReductionIso P.coefficients.l P.extension X n).hom.app _) ≫
    (PurCompactSupport.finiteImageIso P.coefficients.l P.extension n
      (compactification P X)).hom.app _ ≫
    (PurityFiniteSetting.smoothCompactSupport (purAdicFiniteSetting
      P.field P.coefficients P.extension n) (X ↘ Spec (.of P.field.k))).map
        ((scalarReductionDerivedExtension P.coefficients.l P.extension X n).map
            (integralUnitSourceComparison P X d core).inv ≫
          purAdicSourceReduction P.field P.coefficients P.extension
            (X ↘ Spec (.of P.field.k)) d
            (integralTwist P (Spec (.of P.field.k)) (𝟙 _) 0).obj
            (integralTwist P (Spec (.of P.field.k)) (𝟙 _) 0).property n) ≫
    PurityFiniteSetting.coefficientValuedSmoothTrace
      (purAdicFiniteSetting P.field P.coefficients P.extension n)
      (X ↘ Spec (.of P.field.k)) d
      ((scalarReductionDerivedExtension P.coefficients.l P.extension
        (Spec (.of P.field.k)) n).obj
          (integralTwist P (Spec (.of P.field.k)) (𝟙 _) 0).obj)
      (purAdicReductionFiniteTor P.field P.coefficients P.extension
        (Spec (.of P.field.k)) _
          (integralTwist P (Spec (.of P.field.k)) (𝟙 _) 0).property n) ≫
    (PurCompactSupport.finiteReductionIso P.coefficients.l P.extension
      (Spec (.of P.field.k)) n).inv.app _

end WeilConjectures.AdicSmoothDualizing
