/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B7
-/
module

public import Sheaf.Paper.AdicUnitTraceScalarData

/-! # AdicUnitTraceCounitReductions

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

/-- Transposing any prescribed unit lift gives the normalized finite trace at every
positive reduction exponent.

Source: purity transport Steps 2-3; parent unit-trace proof Step 2
(blueprint: lem-pur-unit-trace-counit-reductions).

Proof: expand unitTrace as S.left inverse, compact support of g, then the specified
exceptional counit. Naturality moves reduction of g through compact-support
comparison. The scalar comparison's counit equation identifies the reduced
exceptional counit with the finite counit, and normal.counit identifies the finite
right realization with smoothExceptionalCounit. Substitute the prescribed
reduction equation for sourceUnitIso.hom followed by g.hom. Cancel reduction of
sourceUnitIso against its inverse in HasTraceReductions. The remaining composite
is coefficientValuedSmoothTrace by its definition. All maps are in the finite
coefficient category; the argument applies to every permitted g, including on
empty schemes and in relative dimension zero. -/
theorem unit_trace_counit_reductions
    (normal : FiniteRightNormalization D C E f S)
    (core : CompletedUnitPullback.Core C.l E f)
    (hT : finiteTorConstructibleIntegral C.l E X (tateUnit D C E d X))
    (g : tateUnit D C E d X ≅
      ((operation D C E f S).G.obj ⟨_, core.admissibleY.1⟩).obj)
    (hg : HasPrescribedReductions D C E f d S normal ⟨_, core.admissibleY.1⟩
      ((sourceUnitIso D C E f d core).hom ≫ g.hom)) :
    HasTraceReductions D C E f d core (unitTrace D C E f d S core hT g) := by sorry

end WeilConjectures.PurUnitTrace
