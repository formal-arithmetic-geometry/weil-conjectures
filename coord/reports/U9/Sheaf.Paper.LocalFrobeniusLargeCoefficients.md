## What changed

Proved `WeilConjectures.LocalFrobeniusLarge.stageScalar_existsUnique` using
private proved tensor and naturality helpers. The natural finite-stage H⁰ square
is extended to Ω, then the balanced tensor tower is flattened. Tensor generation
proves the required normalization determines the natural isomorphism uniquely.
The actual coefficient embeddings are checked by cancellation of Shrink equivalences.

All original public signatures, public imports, and definition bodies are retained. No source-library
module is edited. The original node's prior four proof steps remain; an additional
step records this scalar-comparison proof. Exploratory node ownership changes and
the proposed coherence split were withdrawn before delivery.

## Proved and sorry left

Closed one of the two original holes:
`WeilConjectures.LocalFrobeniusLarge.stageScalar_existsUnique`.

The original hole `WeilConjectures.LocalFrobeniusLarge.pointFibre_existsUnique`
remains, with its original statement and proof docstring (node
`def-weil-local-frobenius-trace`). No holes are added and no theorem is split off.
This is a partial proof delivery, not a completion of the common-stage descent.

## No longer needed

No existing import, node, module, declaration, or blueprint unit is withdrawn.
The scalar-comparison proof needs only the two original public imports.
Exploratory imports of PointHeartFiniteStage, AlgebraicClosure, and
StageSystem.Const are omitted from the delivered proof because they serve the
unfinished descent/coherence argument. Dependencies of the original local-trace
proof steps remain needed and are retained.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox report incorrectly described both holes as completed, although
its full proof candidate had not compiled. This report records the verified result.
The attempted common-stage proof reaches the finite-stage cocycle comparison, but
specializing its large transported field structures repeatedly exceeded the
single-file compile limit. The remaining hole is kept at its original declaration;
no equivalent new statement or arbitrary data choice is introduced.

## Second reading by U9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
