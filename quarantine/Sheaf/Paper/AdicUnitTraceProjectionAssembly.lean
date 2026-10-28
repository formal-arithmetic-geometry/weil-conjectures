/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B7
-/
module

public import Sheaf.Paper.AdicUnitTraceConstruction

/-! # AdicUnitTraceProjectionAssembly

Compatibility step for the unit-trace construction. -/

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

/-- A base trace with all normalized finite reductions produces the actual scalar
trace/projection/adjunction construction at each finite coefficient field.

Source: purity transport Steps 2-3; parent unit-trace proof Steps 3-8
(blueprint: lem-pur-unit-trace-projection-assembly).

Proof: choose the canonical ordinary/strict-tower scalar comparison and its Tate
and unit normalizations. Extend the given trace by scalarTrace. At cofinal levels
er, tensor associativity and compact-support scalar comparison identify this with
finite scalar extension of the base trace. Finite universal smooth trace gives
cofinalTrace and equality with the normalized ramified trace. For an arbitrary
positive exponent m, choose er at least m; successive derived quotient and counit
compatibility give traceReductions without flatness of the quotient. Obtain the
normalized j and unit constraint on K-flat representatives using chainJ and
ordinary multiplication. The projection formula is invertible on the finite-Tor
domain. Define each component by the displayed formula of Construction. Projection
naturality, naturality of j, and the adjunction Hom bijection prove that these
components form gamma. The operations and the Hom bijection are coefficient-linear.
Reduce that formula using tensor, source, projection and counit comparisons. The
finite tensor-trace-transpose identity identifies it with the prescribed smooth
purity arrow: at the unit the projection unit equation and the adjunction triangle
identify its transpose with the inverse diagonal orientation. The even shift
contributes sign one. Finite smooth purity makes the first reduction invertible;
derived completeness and derived Nakayama make these actual components invertible.
All Construction fields are these canonical comparisons and the equations just
proved. The formulas also cover the zero input, empty schemes and d=0. -/
theorem unit_trace_projection_assembly
    (core0 : CompletedUnitPullback.Core C.l (baseField D C) f)
    (t0 : (PurCompactSupport.image (PurCompactSupport.completed C.l (baseField D C))
      (integralExceptionalCompactification D f)).obj (tateUnit D C (baseField D C) d X) ⟶
        coefficientUnit D C (baseField D C) Y)
    (ht0 : HasTraceReductions D C (baseField D C) f d core0 t0) :
    Nonempty (Construction D C E f d S t0) := by sorry

end WeilConjectures.PurUnitTrace
