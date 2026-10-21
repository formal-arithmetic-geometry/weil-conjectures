# AlgebraicGeometry.Scheme.automorphism_completion_unit_comparison

## Reason

Complete the original theorem with its entire statement unchanged and prune redundant
imports. Three retained public imports provide every name in the public signature.
Additional proof dependencies are private imports, including access to an existing
private coefficient-equivalence helper by `import all`. No declaration from the
source library is edited, and no new public declaration or proof hole is introduced.

The first delivery preflight requested this record because public imports are removed.
The current direct consumer imports the statement dependencies independently. Its
statement, definitions and proofs require no adaptation. No target statement or
definition changes meaning, so no semantic target re-review is required.

## Old

```lean
public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.IntrinsicCompletionCompleted
public import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
public import Sheaf.Paper.WeilCompletedTensorReflector
public import Sheaf.Paper.PbcAutomorphismTransport
public import Sheaf.Paper.PbcCompletedPullbackActual
public import Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
public import Sheaf.Paper.PbcQbarCompletedPullback
import Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso
import Sheaf.Paper.WeilCompletedKoszulLimitComparison
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.BifunctorShift
```

## New

```lean
public import Sheaf.Paper.WeilCompletedTensorReflector
public import Sheaf.Paper.PbcAutomorphismTransport
public import Sheaf.Paper.PbcCompletedPullbackActual
import all Sheaf.AlgebraicGeometry.ProEtaleOperations
import Sheaf.Paper.SfConstructibleCanonicalCompleteness
import Sheaf.Paper.CompletedKoszulQuotientComparison
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Adjunction.Restrict
```

The signature and visibility of `automorphism_completion_unit_comparison` are
verbatim unchanged. Its former `by sorry` proof is replaced by the complete proof
and proved private helpers. Only import visibility and proof dependencies change.

## Users

`tools/downstream.py Sheaf.Paper.AutomorphismCompletionUnitComparison
--uses automorphism_completion_unit_comparison` lists one downstream module and
exactly two declaration users, including the item itself. The current consumer is
unclaimed in `coord/claims`. It imports `AdicCoefficientDatum`,
`IntrinsicCompletionCompleted`, `ModulePullbackPushforwardAdjunction`, and
`IsoSectionwiseInverseImage` publicly itself, and obtains completed-pullback
interfaces through its own imports. Its call to the item uses the same theorem
statement, including all representatives and the exact unit equation.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.AutomorphismCompletionUnitComparison | E2 | Close its original hole; unchanged public statement, fewer public imports. |
| Sheaf.Paper.CompletedCoefficientPullbackLinearity | unclaimed | Unchanged direct consumer; no adaptation required. |

Ordered remote compilation of the repaired item and the unchanged consumer passed
without warnings (8.4 seconds and 7.4 seconds respectively) in
`scratchpad/consumer-check`. These validation copies are excluded from the delivery
packet. No consumer source is modified or delivered.

## Status

landed 20261021T140806-L-2749575 2026-10-21 (merge of deliver/E2/Sheaf.Paper.AutomorphismCompletionUnitComparison)
