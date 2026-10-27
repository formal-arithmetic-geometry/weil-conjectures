## What changed

Repair of returned head `0a67bf11053`: the mathematics passed review, but landing
rejected a reviewer fix named only `completed-pullback-tensor-unique-choice.md`.
Both change records are included directly at their full `coord/changes/` paths,
with those paths now explicit inside the records. No external basename fix is
required. The landing API expects reviewer override files named
`<stem>.change.md`; the failed override omitted `.change`. The unique-choice
consumer table also now has no blank line splitting its final rows from the table.
Reconciled the node with current `sheaf-dag`, preserving current
metadata and applying only this delivery's proof and Lean-attachment fields.
The current main module still has the original 27 holes and no competing changes;
the retained Lean proof is preserved. `deliver3.py` creates the new commit on the
freshly fetched `sheaf-dag` and runs compilation and preflight before pushing.

Proved `pullbackTensorOrdinaryLimit_rightAdjoint` by the special adjoint functor
theorem: sequence restriction preserves limits because its evaluations are continuous
module pushforwards followed by scalar restrictions, and the sequence module category
is Grothendieck abelian. Added five private proof imports for this argument.

Factored 18 existing uniquely normalized selections through `pullbackTensorUniqueChoice`,
which unfolds to the identical choice operation. Gave `pullbackTensorRoosUnit` its
existing type explicitly, and reused the theorem types for the two scalar-square
condition definitions. Default transparency respects definition boundaries; the six existing proof or
construction bodies that require permissive conversion use local tactic scopes.
Local irreducibility also prevents derived-functor records from expanding. The records are `coord/changes/completed-pullback-tensor-unique-choice.md` and
`coord/changes/completed-pullback-tensor-explicit-types.md`. These changes preserve all
comparison values and
normalization conditions. The change records document their consumers.

Replaced the inverse-image exactness proof's expansive simplification by a functor
equality followed by `integralComparisonSequencePullback_exact`. This changes only
the theorem proof. Serial elaboration and disabling redundant lint passes
keep the elaboration work bounded.

Validation: this packet passed the full delivery axiom probe in 51.8 seconds; with explicit local abelian and countable-product structures in
the Roos lift it passed again in 59.2 seconds,
reporting 101 declarations and exactly the 26 expected original holes. The sole
style warning came from the tool's appended probe text; the module itself has no
lines over 100 characters. Previous delivery attempts timed out and pushed nothing.
Further proof attempts for six other holes remain only in the scratchpad and are
not claimed as delivered.

## Proved and sorry left

Closed one of the 27 original holes:

- `WeilConjectures.pullbackTensorOrdinaryLimit_rightAdjoint`

Added no holes; split off no statements. The following 26 original holes remain,
all attached to `def-pur-completed-pullback-tensor-comparison`:

- `WeilConjectures.pullbackTensorReductionModel_existsUnique`
- `WeilConjectures.pullbackTensorReductionEvaluation_existsUnique`
- `WeilConjectures.pullbackTensorSequenceDirectEvaluation_existsUnique`
- `WeilConjectures.pullbackTensorSequenceInverseEvaluation_existsUnique`
- `WeilConjectures.pullbackTensorRoosModel_existsUnique`
- `WeilConjectures.pullbackTensorPullbackTower_existsUnique`
- `WeilConjectures.pullbackTensorTensorTower_existsUnique`
- `WeilConjectures.pullbackTensorIntegralPullbackModel_existsUnique`
- `WeilConjectures.pullbackTensorReductionGood`
- `WeilConjectures.pullbackTensorIntegralTensorModel_existsUnique`
- `WeilConjectures.pullbackTensorSequenceCochain_existsUnique`
- `WeilConjectures.pullbackTensorSequenceGood`
- `WeilConjectures.pullbackTensorSystemComparison_existsUnique`
- `WeilConjectures.pullbackTensorComparisonCounits`
- `WeilConjectures.pullbackTensorDerivedEvaluation_existsUnique`
- `WeilConjectures.pullbackTensorSystemComparison_evaluation`
- `WeilConjectures.pullbackTensorSystemComparison_associativity`
- `WeilConjectures.pullbackTensorSystemComparison_braiding`
- `WeilConjectures.pullbackTensorSystemComparison_unit`
- `WeilConjectures.pullbackTensorQuotientOrdinary_existsUnique`
- `WeilConjectures.pullbackTensorFiniteGood`
- `WeilConjectures.pullbackTensorQuotient_existsUnique`
- `WeilConjectures.canonicalFinitePullbackTensor_quotient`
- `WeilConjectures.canonicalCommonStagePullbackTensor_existsUnique`
- `WeilConjectures.canonicalIntegralPullbackTensor_scalar`
- `WeilConjectures.canonicalRationalPullbackTensor_scalar`

## No longer needed

No public import, node or module was pruned. Constructing coherent quotient units
is unnecessary for the ordinary-limit adjoint existence proof; the special adjoint
functor theorem proves this existence directly. The remaining normalization statements
still require the quotient constructions in the original plan.

The unsuccessful larger proof packet's development imports are not included:
`Sheaf.AlgebraicGeometry.ProEtaleProductsExact`,
`Sheaf.CategoryTheory.ExactAdjointTowerModels`,
`Sheaf.Paper.CoefficientConstantTowerRoosComparison`,
`Sheaf.CategoryTheory.StrictRoosDerivedLimitComparison`,
`Sheaf.CategoryTheory.StrictRoosDerivation`,
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback`,
`Sheaf.AlgebraicGeometry.VaryingRingOperations`, and
`Mathlib.CategoryTheory.Localization.Predicate`.
These modules remain relevant to the original unproved obligations.

## Where the brief, the DAG or earlier work was wrong

The previous landing used a repository basename for a reviewer change-record
override. `tools/batch_land.py` requires `<stem>.change.md` for those overrides.
The repaired packet includes the corrected record directly and documents this
convention; no launcher or landing tool was modified.

Ordinary-limit adjoint existence does not require constructing quotient units.
The unchanged source module also exceeded the current 60-second compile limit.
Profiling found expensive normalization-predicate and derived-record unfolding;
definitionally identical wrappers and explicit types make the one-hole packet compile.
The six other tentative proofs did not pass a full-file compile, so they are excluded.

## Second reading by J6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
