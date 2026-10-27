# StrictPullbackEvaluationConstructor proof imports

## Reason

The returned global build failed at lines 107 and 118 of the constructor with
unknown identifiers `AmbientPullbackTensor.sequencePushEvaluation` and
`SequenceModuleEvaluation.sequenceModulePullbackEvaluation_isIso`. The subsequent
identity-on-sections errors at lines 141 and 144 depend on the unresolved former
definition. The private direct-image comparison moved verbatim from the item to
`AmbientPullbackSiteData`; `import all` of the item does not expose private
declarations of the publicly reexported construction module. The evaluation
theorem also needs an explicit proof import.

The consumer node replaces the final coherence dependency by
`lem-sf-ambient-pullback-site-constructions` in its proof step and proof_deps,
matching the defining module now imported. Its statement, Lean attachment and
all remaining dependencies stay unchanged.

All twenty module entries in the return name this same consumer failure. No
generic scalar lemma needs to change: the problem is this consumer's proof
visibility after relocation.

## Old

```lean
public import Sheaf.Paper.StrictQuotientExpressions
import all Sheaf.Paper.AmbientPullbackTensorCoherence
import Sheaf.AlgebraicGeometry.ProEtaleCoefficientPullbackExact
```

## New

```lean
public import Sheaf.Paper.StrictQuotientExpressions
import all Sheaf.Paper.AmbientPullbackSiteData
import Sheaf.CategoryTheory.SequenceModulePullbackEvaluation
import Sheaf.AlgebraicGeometry.ProEtaleCoefficientPullbackExact
```

The current main has independently removed the redundant PointwiseLeftDerived
proof import. Preserve that removal when rebasing this forced adaptation.
Only these proof import lines change. Every declaration, public import,
signature, definition body, proof, attribute and instance in the consumer stays
verbatim. The original `directEvaluation_apply` proof remains `rfl` for the
original comparison construction. No target or mathematical meaning changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.StrictPullbackEvaluationConstructor | unclaimed | Import the defining module's private comparison explicitly and the generic evaluation theorem directly. Public interface unchanged. |

The other current `import all` users of the relocated ambient and integral
modules are checked against the packet, including `StrictScalarPullbackComparison`
and the five integral consumers. Unchanged check copies are removed before
delivery. This adaptation changes no consumer interface, so it requires no
adaptation of the constructor's importers.

## Status

landed 20261027T205959-L-1641374 2026-10-27 (merge of deliver/G2/Sheaf.Paper.AmbientPullbackTensorCoherence)
