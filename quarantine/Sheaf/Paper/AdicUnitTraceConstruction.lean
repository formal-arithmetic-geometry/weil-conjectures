/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Sheaf.Paper.AdicUnitTraceScalarData

/-! # Unit trace transpose construction data

Source: current blueprint, purity transport Steps 2-3 and unit-trace assembly
(blueprint: def-pur-unit-trace-construction).

The actual projection and exceptional-adjunction assembly and its properties.
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

set_option genSizeOf false in
set_option genSizeOfSpec false in
set_option genInjectivity false in
set_option genCtorIdx false in
/-- The actual trace/projection/adjunction construction, with its canonical
coordinate comparisons, naturality, coefficient linearity, prescribed reductions
and invertibility. All data are supplied by the main theorem.
Source: current blueprint purity transport, Steps 2-3 and unit-trace assembly
(blueprint: def-pur-unit-trace-construction). -/
structure Construction
    (t0 : (PurCompactSupport.image (PurCompactSupport.completed C.l (baseField D C))
      (integralExceptionalCompactification D f)).obj (tateUnit D C (baseField D C) d X) ⟶
        coefficientUnit D C (baseField D C) Y) where
  normal : FiniteRightNormalization D C E f S
  core : CompletedUnitPullback.Core C.l E f
  coefficients : PurAdicScalarTrace.CoefficientComparison C.l (baseField D C) E
    (baseInclusion D C E) D C.different (integralExceptionalCompactification D f) d
  models : RingedModels C.l E
  openComparison : RingedOpenComparisons C.l E models
  tateFiniteTor : finiteTorConstructibleIntegral C.l E X (tateUnit D C E d X)
  lineKFlat : (lineComplex D C E d X).IsKFlatIndependentCoefficients
  unitKFlat : (unitComplex D C E Y).IsKFlatIndependentCoefficients
  unitIso : coefficientUnit D C E Y ≅
    (calculus C.l E Y).integralClosed.monoidal.tensorUnit
  unitNormalized : IsUnitNormalized D C E Y unitKFlat unitIso
  j : sourceRestricted D C E f d ≅ tensorFunctor D C E f d
  jNormalized : IsJNormalized D C E f d models lineKFlat j
  completionIso : ∀ K : finiteTorConstructibleIntegralCategory C.l E Y,
    IsIso (((models.tensor Y).chi C.l E).app
      ((PurCompactSupport.image (PurCompactSupport.completed C.l E)
        (integralExceptionalCompactification D f)).obj (tateUnit D C E d X), K.obj))
  tensorFiniteTor : ∀ K : finiteTorConstructibleIntegralCategory C.l E Y,
    finiteTorConstructibleIntegral C.l E X ((tensorFunctor D C E f d).obj K)
  projectionIso : ∀ K : finiteTorConstructibleIntegralCategory C.l E Y,
    IsIso (adicProjection C.l E models openComparison
      (integralExceptionalCompactification D f) (tateUnit D C E d X) K.obj (completionIso K))
  gamma : sourceRestricted D C E f d ⟶
    (operation D C E f S).G ⋙ (finiteTorConstructibleIntegral C.l E X).ι
  formula : ∀ K : finiteTorConstructibleIntegralCategory C.l E Y,
    gamma.app K = j.hom.app K ≫
      adicTranspose D C E f S (integralExceptionalCompactification D f)
        ⟨_, tensorFiniteTor K⟩ K
        (adicTraceMap C.l E models openComparison
          (integralExceptionalCompactification D f) (tateUnit D C E d X) K.obj
          (completionIso K) (projectionIso K)
          (scalarTrace D C E f d coefficients t0 ≫ unitIso.hom))
  reductions : ∀ K : finiteTorConstructibleIntegralCategory C.l E Y,
    HasPrescribedReductions D C E f d S normal K (gamma.app K)
  invertible : ∀ K : finiteTorConstructibleIntegralCategory C.l E Y, IsIso (gamma.app K)
  sourceLinear : (sourceRestricted D C E f d).Linear (Padic.coefficientExtensionIntegers C.l E)
  adjunctionLinear : ∀ (A : finiteTorConstructibleIntegralCategory C.l E X)
    (K : finiteTorConstructibleIntegralCategory C.l E Y)
    (a : Padic.coefficientExtensionIntegers C.l E)
    (v : (operation D C E f S).F.obj A ⟶ K),
    ((operation D C E f S).adjunction.homEquiv A K) (a • v) =
      a • ((operation D C E f S).adjunction.homEquiv A K) v
  supportLinear : (operation D C E f S).F.Linear (Padic.coefficientExtensionIntegers C.l E)
  exceptionalLinear : (operation D C E f S).G.Linear (Padic.coefficientExtensionIntegers C.l E)
  traceReductions : HasTraceReductions D C E f d core (scalarTrace D C E f d coefficients t0)
  cofinalTrace : ∀ (n r : ℕ) (hr : 1 ≤ r),
    n + 1 = (purAdicFiniteSetting D C E n).ramificationIndex * r →
      CofinalFiniteTraceCompatibility (purAdicFiniteSetting D C E n) f d r hr


end WeilConjectures.PurUnitTrace
