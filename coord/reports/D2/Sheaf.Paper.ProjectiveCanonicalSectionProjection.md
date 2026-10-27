## What changed

The assigned theorem now compiles as a composition of two named lower steps. The core
section/projection coherence is stated in `CanonicalSectionProjectionCore`, and the
supported-unit normalization step is stated in `CanonicalSectionProjectionTransport`.
The item module imports the transport module and closes its original theorem by applying
these two declarations.

## Proved and sorry left

Closed `AlgebraicGeometry.ProEtale.RationalP1.canonical_section_projection` (1 of 1
sorries in the assigned module). Added the strictly simpler intermediate declarations
`canonical_section_projection_core` and `canonical_section_projection_transport`; their
proofs remain `sorry` for follow-up workers.

## No longer needed

No declared dependency was removed. The attempted local projection-naturality helper
was unnecessary after the transport step was isolated, so no additional import was kept.

## Where the brief, the DAG or earlier work was wrong

The original DAG bundled the categorical section/projection coherence and the subsequent
supported-source isomorphism transport into one theorem. The two operations cross the
project's opaque internal tensor-instance boundary differently, so they are recorded as
two separate strictly simpler steps here.

## New nodes

- `lem-sfb-projective-canonical-section-projection-core`: the regular-coefficient
  section/projection coherence before supported-source transport.
- `lem-sfb-projective-canonical-section-projection-transport`: the coefficient-normalization equality transporting the normalized composite
  across `supportedUnitIso`, before applying the core identity.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.CanonicalSectionProjectionCore": "9328a197fcfc80183072be027d23908f5c5f697a", "Sheaf.Paper.CanonicalSectionProjectionTransport": "8f6932ad8bcf900e6db474774b5f0a83615a3290", "Sheaf.Paper.ProjectiveCanonicalSectionProjection": "ded45890ab97df5d51dfcf39d0dd69a0a60f112c"}, "results": {"Sheaf.Paper.ProjectiveSupportedSectionProjection": {"hash": "1f4e9827eddc9de852380fd0121d596fc2cea5e4", "status": "OK"}}, "seconds": 17, "time": "2026-10-28T04:26:04+0800", "transitive": 0, "version": 1}
```

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
