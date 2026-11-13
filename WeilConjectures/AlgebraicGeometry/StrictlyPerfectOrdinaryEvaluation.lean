/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.BoundedOrdinaryEvaluationAssembly

/-! # Ordinary evaluation for a strictly perfect complex

## References

* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 08DM](https://stacks.math.columbia.edu/tag/08DM)
-/

@[expose] public section

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

/-- Ordinary evaluation is degreewise invertible for a strictly perfect first input.
There is no bound on the second complex and the open need not be affine. -/
theorem isIso_localOrdinaryEvaluation_degree (X : Scheme.{u}) (U : X.Opens)
    (P F : CochainComplex (localEvaluationModules X U) ℤ)
    (hstrict : Scheme.IsStrictlyPerfect X U P)
    (f : localEvaluationTensor X U P F ⟶ homComplex (R := X.sheaf.over U) P F)
    (hf : IsLocalOrdinaryEvaluation X U P F f) (n : ℤ) : IsIso (f.f n) := by
  apply boundedOrdinaryEvaluation_degree X U P F hstrict.1 ?_ n f hf
  intro r B
  exact SheafOfModules.isIso_moduleDualEvaluation_of_retract
    (X.sheaf.over U) (P.X r) B (hstrict.2 r)

end AlgebraicGeometry
