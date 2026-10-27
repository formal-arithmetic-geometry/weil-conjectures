## What changed

Proved `WeilConjectures.commonStageTensorRightUnitor_naturality` without changing its
statement, definitions, or public imports. Added a proof import of
`Sheaf.Paper.IntegralSystemReductionFullyFaithful` and proved private helpers for
counit naturality, the natural tensor-reduction comparison, integral and rational
right-unitor naturality, and commuting a unit comparison past a tensor arrow.
The final argument compares representatives at one common coefficient stage.
Updated the node proof and dependencies to describe this calculation.
Local reducibility settings expose the stage alias and its stage projection for
category simplification while preserving the transparency checks.

Validation: the complete file compiled through `lcompile.py` in 48 seconds with
profiling enabled. Removed the profiling options before delivery.

## Proved and sorry left

Closed the one hole in `WeilConjectures.commonStageTensorRightUnitor_naturality`
(node `lem-pur-common-stage-tensor-right-unitor-natural`). Added zero holes.
No `sorry` remains in the delivered module. This proof uses existing specifications
of tensor operations and constraints; it does not claim those dependencies are
already free of `sorry`.

## No longer needed

No original Lean import was removed and no module is withdrawn.
The direct proof dependency `lem-coef-completed-tensor-scalar-linearity`
(`Sheaf.Paper.CompletedTensorScalarLinearity`) is unnecessary here: the existing
rational tensor specification already supplies its bilinear extension and its
pure-tensor formula. This removes this node's direct dependency, without claiming
that other consumers no longer need scalar linearity.
The final square needs no extra scalar tower or scalar unit equation: the
prescribed comparisons are available at the same stage, and functoriality and
inverse cancellation suffice.

## Where the brief, the DAG or earlier work was wrong

The DAG's proof is valid but its last step asks for more scalar-coherence work
than the stated representative specifications require. Their universal stage
formulas reduce the square directly to rational naturality. The unit record
`sk-prop-an` has no realization attached to this auxiliary node; the unit's
statement and route are preserved. No statement or definition repair was needed.

## Second reading by V1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
