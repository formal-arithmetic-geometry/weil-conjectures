/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q111
-/
module

public import Sheaf.Paper.AdicPurityScalarNaturalityData

/-! # Integral purity assembly

Source: purity transport Steps 2--3.
(blueprint: lem-pur-adic-purity-scalar-naturality). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.AdicPurityScalarNaturality

variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)

variable {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (d : ℕ) [SmoothOfRelativeDimension d f]

attribute [local irreducible] source target scalar associator scalarUnit
  targetShift composeShift

/-- Construct the normalized purity transposes with the scalar square and shifts.
The source tensor cocycle and the exceptional tensor cocycle are not conclusions
of this construction lemma.
Source: purity transport Steps 2--3, reconstructed unit trace and scalar trace calculus
(blueprint: lem-pur-adic-normalized-comparison-construction).

Proof: obtain a normalized coefficient System from exists_system, retaining the
finite right-adjoint Hom-transpose normalization in fixed-scalar coordinates.
Use operationDomains, scalar_preserves, source_exact_linear and scalar_exact to
restrict the actual operations and give OperationData; finite dimensionality of
finite-type schemes supplies the dimension bounds. Conjugate the published scalar
comparisons by scalarBridge to obtain c and the full lift of sourceScalarComponent
to obtain a. Their component normalizations give cCanonical and aCanonical.
Apply adic_unit_trace_transpose_reductions to the base-field coefficient unit,
choose its reconstructed orientation and extend that one trace to every finite
coefficient field. Its Construction supplies natural invertible transposes with
prescribed finite reductions. Transport through the normalized exceptional
realization; the coefficient adjunction counit equation identifies its reduction
with targetReductionMap and pins finiteRightNormalized independently of gamma.
Lift the natural components through the fully faithful finite-Tor inclusion to
obtain gamma and the exceptional realization. The Construction reduction formula
gives finiteReductions, and normalization gives targetRealizationReductions.
Conjugate the recorded exceptional mate by scalarBridge to define b; the Hom
transpose formula gives bMate. Scalar_trace_coherence for extensions of this one
trace, followed by coefficient_calculus, gives the displayed purity square after
cancelling the canonical tensor-coordinate comparisons. No arbitrary lifts are
identified from their reductions. Finally adicProjectionShiftCoherence supplies
the projection and adjoint shift identities for these very traces. Shift_calculus
and the canonical source reassociation give gamma shift compatibility. All scalar
maps and realizations are fixed before this comparison, so no coefficient-dependent
automorphism is absorbed into the finite reductions. Empty schemes and d=0 are
included by the same unit/projection formulas. -/
theorem normalizedComparisonConstruction :
    ∃ (S : ConstructibleExceptionalCoefficients.System C.l C.Qbar D C.different (f := f))
      (P : ComparisonData D C f d S),
    (∀ (E F : Field D C) (h : E ≤ F) (K : Cat D C E Y),
    (scalar D C P.scalarClosed E F h true).map ((P.gamma E).hom.app K) ≫
        (P.b E F h).hom.app K =
      (P.a E F h).hom.app K ≫
        (P.gamma F).hom.app ((scalar D C P.scalarClosed E F h false).obj K)) ∧
    (∀ (E : Field D C),
    ShiftCompatibility (source D C f d E) (target D C f S E)
      (sourceShift D C f d E) (targetShift D C f S E) (P.gamma E)) := by
  sorry

end WeilConjectures.AdicPurityScalarNaturality
