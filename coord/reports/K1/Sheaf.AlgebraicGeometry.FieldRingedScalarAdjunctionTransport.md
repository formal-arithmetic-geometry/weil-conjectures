## What changed

Repaired the quarantined module's elaboration against the current dependency interfaces.
Added a local `EssentiallySmall.{u + 1}` instance for pro-etale sites, fixing the
universe metavariables in the balanced tensor and derived normalization declarations.
Scoped a larger synthesis heartbeat limit to `ScalarRepresentativeNormalization`,
whose existing tensor-colimit instance search otherwise timed out. The target theorem
statement and its single `sorry` are unchanged.

## Proved and sorry left

No holes were closed (rework repair). The existing hole remains:
`AlgebraicGeometry.ProEtale.FieldActionTransport.field_ringed_scalar_adjunction_transport`.
No new holes were added. The repaired module compiles in 29.2 seconds.

## No longer needed

None. All imports and declarations from the quarantined module remain in use.

## Where the brief, the DAG or earlier work was wrong

The previous delivery was blocked before elaboration because the published
`Sheaf.Paper.WeilTensorProduct.olean` artifact was unavailable. Once the dependency
interface was available, the recorded universe and synthesis failures were repaired
locally as above; no statement or DAG change was required.

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
