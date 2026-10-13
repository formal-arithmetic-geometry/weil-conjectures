# Sheaf.FieldTheory.TriangularFieldModelEvaluationKernel imports

## Reason

The quotient-operations import is used only by the evaluation-kernel proof, so
it must not be public. It can be removed entirely: the new normal-form module
publicly imports quotient-basic for its statement, making quotient-zero
membership available to the proof. The target theorem's signature, the equation
definition and all existing declaration visibilities stay unchanged.

## Old

```lean
public import Sheaf.FieldTheory.TriangularFieldModelEquations
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.Algebra.Polynomial.Monic
```

## New

```lean
public import Sheaf.FieldTheory.TriangularFieldModelEquations
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.Algebra.Polynomial.Monic
import Sheaf.FieldTheory.TriangularFieldModelData
import Sheaf.FieldTheory.TriangularFieldModelNormalForm
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.FieldTheory.TriangularFieldModelPresentation | unclaimed in local snapshot | Unchanged original compiled via lcompile.py against all three delivered modules, including the reduced public import set; no adaptation required. |

This is the sole direct importer in the source snapshot. It already has its own
public quotient-operations import, and continues to export it to all of its
importers. Thus no transitive importer loses access to quotient operations, and
no target statement meaning or definition changes. No target statement review
is reopened by this import-only repair.

## Status

landed 20261013T113357-L-3188781 2026-10-13 (merge of deliver/V1/Sheaf.FieldTheory.TriangularFieldModelEvaluationKernel)
