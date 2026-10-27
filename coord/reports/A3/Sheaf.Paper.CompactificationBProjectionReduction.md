## What changed

Re-delivery after the prior landing was removed for a deterministic heartbeat timeout
in the final naturality proof. The theorem proof and the three supporting modules are
restored from the reviewed delivery. The final rewrite now applies `congrArg` to the
ordinary naturality equality and simplifies the functorial composition once, avoiding
the expensive repeated `rw` elaboration. The public theorem and all supporting
signatures are unchanged. The associated change record is `coord/changes/Z7-compactification-b-projection-presentation.md`.

## Proved and sorry left

The original hole in
`AlgebraicGeometry.ProEtale.CompactificationBProjection.compactification_b_projection_reduction`
is closed. The two supporting public theorem holes remain as the strictly smaller
split statements `completion_projection_domains` and
`ordinary_projection_reduction_square`. No additional holes were added in this repair.

## No longer needed

No further imports or nodes were pruned in this repair. The three supporting modules
and the moved coordinate definitions remain required by the proof.

## Where the brief, the DAG or earlier work was wrong

The earlier reviewed proof was mathematically complete but its final `rw` sequence
exceeded the default heartbeat limit during global verification. Replacing that
sequence with a single mapped congruence preserves the same categorical argument
while compiling within the file limit.

## New nodes

None. The two split theorem nodes and the coordinate definition node were created and
reviewed in the earlier delivery and are unchanged here.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
