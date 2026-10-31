/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicUnitTraceTensorCoordinates

/-! # Unit and scalar-extended traces

Source: current blueprint, purity transport Steps 2-3 and unit-trace assembly
(blueprint: def-pur-unit-trace-scalar-data).

The exceptional unit trace, its scalar extension and finite trace compatibility.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open WeilConjectures.IntegralSystemRealization
namespace WeilConjectures.PurUnitTrace
open ConstructibleExceptionalCoefficients
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
  (S : RingSystem C.l C.Qbar D C.different (f := f))

/-- Apply actual compact support to g0 and then the specified exceptional counit.
Source: current blueprint purity transport, Steps 2-3 and unit-trace assembly
(blueprint: def-pur-unit-trace-scalar-data). -/
def unitTrace (core : CompletedUnitPullback.Core C.l E f)
    (hT : finiteTorConstructibleIntegral C.l E X (tateUnit D C E d X))
    (g : tateUnit D C E d X ≅
      ((operation D C E f S).G.obj ⟨_, core.admissibleY.1⟩).obj) :
    (PurCompactSupport.image (PurCompactSupport.completed C.l E)
      (integralExceptionalCompactification D f)).obj (tateUnit D C E d X) ⟶
        coefficientUnit D C E Y :=
  (S.left (integralExceptionalCompactification D f) (.integral {carrier := E})).inv.app
      ⟨_, hT⟩ ≫
    ((operation D C E f S).F.map (ObjectProperty.homMk g.hom)).hom ≫
    ((operation D C E f S).adjunction.counit.app ⟨_, core.admissibleY.1⟩).hom

/-- The reduction of a trace equals the recorded finite coefficient-valued smooth
trace at the reduced unit. The displayed source comparison is the prescribed
source reduction and normalized pulled-unit isomorphism.
Source: current blueprint purity transport, Steps 2-3 and unit-trace assembly
(blueprint: def-pur-unit-trace-scalar-data). -/
def HasTraceReductions (core : CompletedUnitPullback.Core C.l E f)
    (t : (PurCompactSupport.image (PurCompactSupport.completed C.l E)
      (integralExceptionalCompactification D f)).obj (tateUnit D C E d X) ⟶
        coefficientUnit D C E Y) : Prop :=
  ∀ n : ℕ, HEq
    ((PurCompactSupport.comparison
        (PurCompactSupport.reduction C.l E (n + 1) (Nat.succ_pos n))
        (integralExceptionalCompactification D f)).app (tateUnit D C E d X) ≫
      (PurCompactSupport.image (PurCompactSupport.finite C.l E (n + 1)
        (Nat.succ_pos n)) (integralExceptionalCompactification D f)).map
          ((PurCompactSupport.finiteReductionIso C.l E X n).hom.app _) ≫
      (PurCompactSupport.finiteImageIso C.l E n
        (integralExceptionalCompactification D f)).hom.app _ ≫
      (PurityFiniteSetting.smoothCompactSupport (purAdicFiniteSetting D C E n) f).map
        ((scalarReductionDerivedExtension C.l E X n).map
            (sourceUnitIso D C E f d core).inv ≫
          purAdicSourceReduction D C E f d (coefficientUnit D C E Y)
            core.admissibleY.1 n) ≫
      PurityFiniteSetting.coefficientValuedSmoothTrace (purAdicFiniteSetting D C E n) f d
        ((scalarReductionDerivedExtension C.l E Y n).obj (coefficientUnit D C E Y))
        (purAdicReductionFiniteTor D C E Y _ core.admissibleY.1 n))
    ((PurCompactSupport.finiteReductionIso C.l E Y n).hom.app _ ≫
      (scalarReductionDerivedExtension C.l E Y n).map t)

/-- The base coefficient field inside the fixed algebraic closure, represented
by the bottom intermediate field, hence canonically isomorphic to Q_l.
Source: current blueprint purity transport, Steps 2-3 and unit-trace assembly
(blueprint: def-pur-unit-trace-scalar-data). -/
abbrev baseField : IntermediateField (Padic C.l) C.Qbar := ⊥

/-- The unique inclusion of the base intermediate field into E.
Source: current blueprint purity transport, Steps 2-3 and unit-trace assembly
(blueprint: def-pur-unit-trace-scalar-data). -/
def baseInclusion : (baseField D C) →ₐ[Padic C.l] E :=
  IntermediateField.inclusion bot_le

/-- The trace extended from Q_l using the published multiplication-normalized
unit comparison, canonical twist/shift comparison and inverse support mate.
Source: current blueprint purity transport, Steps 2-3 and unit-trace assembly
(blueprint: def-pur-unit-trace-scalar-data). -/
def scalarTrace
    (a : PurAdicScalarTrace.CoefficientComparison C.l (baseField D C) E
      (baseInclusion D C E) D C.different (integralExceptionalCompactification D f) d)
    (t0 : (PurCompactSupport.image (PurCompactSupport.completed C.l (baseField D C))
      (integralExceptionalCompactification D f)).obj (tateUnit D C (baseField D C) d X) ⟶
        coefficientUnit D C (baseField D C) Y) :
    (PurCompactSupport.image (PurCompactSupport.completed C.l E)
      (integralExceptionalCompactification D f)).obj (tateUnit D C E d X) ⟶
        coefficientUnit D C E Y :=
  (PurCompactSupport.image (PurCompactSupport.completed C.l E)
    (integralExceptionalCompactification D f)).map (twistedUnitIso D C E d X).inv ≫
  PurAdicScalarTrace.trace C.l (baseField D C) E (baseInclusion D C E)
    D C.different (integralExceptionalCompactification D f) d a
      ((PurCompactSupport.image (PurCompactSupport.completed C.l (baseField D C))
        (integralExceptionalCompactification D f)).map
          (twistedUnitIso D C (baseField D C) d X).hom ≫ t0)


open PurityFiniteSetting in
/-- The finite universal smooth-trace equation at a cofinal exponent er.
The coefficient and root comparisons retain precisely the published normalization;
this proposition packages that equation for the integral trace conclusion.
Source: current blueprint purity transport, Steps 2-3 and unit-trace assembly
(blueprint: def-pur-unit-trace-scalar-data). -/
def CofinalFiniteTraceCompatibility (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [IsSeparated (Y ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) [SmoothOfRelativeDimension d f] (r : ℕ) (hr : 1 ≤ r) : Prop :=
    ∃ (eA : (primeTraceSetting P r hr).Ring ≃+*
        ULift.{u} (ZMod (primeTraceSetting P r hr).diagonalExponent))
      (hB : ((primeTraceSetting P r hr).diagonalExponent : P.Ring) = 0)
      (hA : (P.diagonalExponent : (primeTraceSetting P r hr).Coefficient) = 0)
      (q : X.rootsOfUnitySheaf P.diagonalExponent ⟶
        X.rootsOfUnitySheaf (primeTraceSetting P r hr).diagonalExponent)
      (a : finiteEtaleTateLine X P.diagonalExponent
          (primeTraceSetting P r hr).Coefficient hA ≅
        finiteEtaleTateLine X (primeTraceSetting P r hr).diagonalExponent
          (primeTraceSetting P r hr).Coefficient
          (primeTraceSetting P r hr).diagonalExponent_annihilates)
      (σ : Etale.FiniteSmoothPurity.CoefficientLineComparison
        (finiteGeneralRingCoefficientMap (primeTraceSetting P r hr) P.Ring hB eA).ulift
        P.diagonalExponent P.diagonalExponent hA P.diagonalExponent_annihilates X),
      FiniteGeneralRingKummerComparison (primeTraceSetting P r hr).Coefficient
        P.diagonalExponent (primeTraceSetting P r hr).diagonalExponent
        hA (primeTraceSetting P r hr).diagonalExponent_annihilates X q a ∧
      σ.roots = 𝟙 _ ∧
      (∀ M : proEtaleDerivedCategory X (primeTraceSetting P r hr).Ring,
        finiteTorConstructible (primeTraceSetting P r hr).coefficients.l
          (primeTraceSetting P r hr).extension
          r hr X M →
        IsIso (traceCompactComparison P f r hr
          (finiteGeneralRingCoefficientMap (primeTraceSetting P r hr) P.Ring hB eA) M)) ∧
      traceCompactComparison P f r hr
          (finiteGeneralRingCoefficientMap (primeTraceSetting P r hr) P.Ring hB eA)
          (traceTwist (primeTraceSetting P r hr) X d) ≫
        (smoothCompactSupport P f).map
          (traceTwistExtensionIso P (primeTraceSetting P r hr)
            (finiteGeneralRingCoefficientMap (primeTraceSetting P r hr) P.Ring hB eA)
            X d hA a σ).hom ≫
        traceOnTwist P f d =
      (scalarExtensionFunctor
          (finiteGeneralRingCoefficientMap (primeTraceSetting P r hr) P.Ring hB eA) Y).map
        (traceOnTwist (primeTraceSetting P r hr) f d) ≫
        (traceUnitExtensionIso P
          (finiteGeneralRingCoefficientMap (primeTraceSetting P r hr) P.Ring hB eA) Y).hom


end WeilConjectures.PurUnitTrace
