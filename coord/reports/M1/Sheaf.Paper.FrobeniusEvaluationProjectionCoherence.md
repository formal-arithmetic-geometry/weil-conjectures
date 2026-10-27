## What changed

Completed the two remaining proofs in Sheaf.Paper.FrobeniusEvaluationProjectionCoherence.
transport_exists converts the existing canonical pullback tensor comparisons and normalized
open tensor comparison into the original Transport record. open_square converts its supplied
data to the existing clopen tensor interface and applies cartesian_tensor, using the identity
open only to fill the auxiliary fields absent from that equation. The private transportData
helper explicitly constructs the Data record, retaining the supplied first three fields, and
proves its composite-open inverse-transpose equation by naturality and the composite unit
formula. All existing public signatures, comparison records and definitions are unchanged.

Added proof-only imports of CanonicalPullTensor, ClopenCartesianTensorSquare and
ClopenComparisonTensorSquareDataExistence (the last with import all for its proved private
open_tensor_exists helper). Updated the node's proof and proof dependencies to this route.

## Proved and sorry left

Closed both original holes (2 of 2):
- WeilConjectures.PodEvaluationProjection.OpenSquare.transport_exists.
- WeilConjectures.PodEvaluationProjection.OpenSquare.open_square.

No sorry remains in the item. No holes or declarations with postponed proofs were added.
Existing canonical_pull_tensor, pullback_tensor_compatibility, the open tensor support
comparison and the reverse clopen adjunction remain obligations in their existing modules;
their existing declarations are used as the stage-3 brief permits.

## No longer needed

No module is withdrawn and no existing import is removed. The direct proof dependency
lem-sf-integral-compactification-system-realization is no longer used: realized_open_square
already applies the supplied realization functor to the system-level equation. Its module
was not directly imported. The direct Step 3 dependence on
lem-pur-derived-pullback-tensor-iso is replaced by the existing canonical tensor pullback
and Cartesian square interface; that module remains a public import used by the evaluation
signatures and comparisons. No unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The old Step 3 plan did not name the already stated equivalent clopen tensor interfaces.
They apply to an arbitrary normalized square and arbitrary additional open; choosing the
identity open supplies the unused auxiliary data without any properness, separatedness,
quasi-compactness or coefficient flatness assumption on the original square. The original
records retain their exact data and normalization, including both modes. No statement or
definition repair was needed.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
