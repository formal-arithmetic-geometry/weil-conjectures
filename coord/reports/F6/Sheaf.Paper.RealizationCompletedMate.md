## What changed

Proved `AlgebraicGeometry.Scheme.realizationCompletedMate` with its statement and all public
imports unchanged. All new helpers are proved private lemmas in the item module. No other
module or definition changes. Local elaboration controls are recorded in
`coord/changes/realization-completed-mate-local-elaboration.md`, as required by preflight.

The proof uses the existing generic `AdicCoefficientDatum.completedExchange_unit` identity.
For invertibility of its two specified completion units, proper direct image preserves actual
coefficient constructibility. Ordinary pullback preserves the actual-ring local perfect models:
the proof constructs the pulled-back stratification and covering sieves, then transports each
model by ordinary pullback composition and the existing constant-model isomorphism. Intrinsic
tower completeness and the first target-augmentation identity make the specified units
invertible. Cancellation gives the required formula.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.realizationCompletedMate` (1 original hole).
Added holes: none. Split off: none. Sorries remaining in the delivered module: zero.
Existing imported theorem holes remain their original items; no proofs are claimed for them.
The full item compiled cleanly with the normal settings in 14.5 seconds through
`lcompile.py`. There are no warnings. The first preflight required a record for local
attribute commands; that record is now included. Final delivery checks are pending.

## No longer needed

Removed the proof import `Sheaf.Paper.OrdinaryCompletedIntegralPullback` and the corresponding
planned dependency `lem-tw-ordinary-completed-integral-pullback`.
The proof also does not use the planned `lem-weil-pbc-proper-integral-ordinary-inputs`
(`Sheaf.Paper.ProperIntegralOrdinaryInputs`) or
`lem-weil-pbc-completed-source-augmentation-normalization`
(`Sheaf.Paper.CompletedSourceAugmentationNormalization`). The existing generic unit equation
already gives the needed exchange identity, and the actual-ring local model criterion avoids
coefficient-presentation transports through the detailed lifted category.
These are dependencies pruned from this item, not claims that the modules have no other users.
No module is withdrawn or deleted.

Removed obsolete tool approvals from this node for
`lem-sfb-finite-proper-geometric-cd-bound`, `lem-tw-ordinary-completed-integral-pullback`, and
`lem-weil-pbc-proper-fp-permanence`. The geometric dimension argument uses only the existing
finite-type dimension bound and field-extension dimension invariance, not cohomological
vanishing. The existing approval `def-weil-l-adic-coefficient-extension` remains.

## Where the brief, the DAG or earlier work was wrong

The planned `pbc_proper_integral_ordinary_inputs` and
`ordinaryCompletedIntegralPullback` use `E : Type u` and the lifted coefficient ring
`PbcIntegralRing l E`. This item uses `E : Type (u + 1)` and the actual unlifted valuation
ring. They cannot be applied directly. The proof uses existing actual-ring interfaces instead;
no signature is weakened or universe changed. Its statement matches the node, including
specified unit homs and ordered strict exchange, and keeps the fixed unit route.

The proof uses as tools `lem-fin-finite-type-fibre-dimension-bound` and
`lem-kun-dimension-extension` for the geometric bound, and the proved constant-pullback helper
of `lem-cbc-extension-zero-perfect-model-transport` for the actual local models. These are
ordinary dimension/model transport facts; they do not bypass a unit theorem. Any newly needed
cross-unit tool approvals are for the maintainer to record. None were added to `tool_uses`.

## Second reading by F6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
