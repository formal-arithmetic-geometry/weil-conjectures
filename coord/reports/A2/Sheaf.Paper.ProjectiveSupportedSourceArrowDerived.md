## What changed

Filled the original `supported_source_arrow_derived` proof by reducing it to a
strictly simpler residual compatibility theorem in the same module. The completed
proof composes the residual equation with the support isomorphism and cancels its
inverse/hom composite using functoriality. Added one plain proof theorem with a
named `sorry`, `supported_source_arrow_derived_core`, because the canonical
right-derived compatibility itself is not available in the current library.
The module compiled successfully with `lcompile.py`.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.RationalP1.supported_source_arrow_derived`.

Added one strictly simpler split-off hole:
`AlgebraicGeometry.ProEtale.RationalP1.supported_source_arrow_derived_core`,
node `lem-sfb-projective-supported-source-arrow-derived-core`.
No definitions contain `sorry`.

## No longer needed

The original planned proof dependencies remain the dependencies of the split-off
core theorem. No imports were removed and no existing modules were withdrawn.
The parent node now depends directly on the new core node; the parent no longer
lists the five low-level declarations as direct proof dependencies.

## Where the brief, the DAG or earlier work was wrong

The stated low-level declarations do not expose a finished theorem expressing the
full canonical derived-unit compatibility. The final cancellation is short once
that compatibility is isolated, so the unresolved part was split into one strictly
smaller named theorem rather than leaving a partial proof. The target statement,
its hypotheses, and the unit route are unchanged.

## New nodes

`lem-sfb-projective-supported-source-arrow-derived-core` records the residual
canonical derived compatibility and is realized by
`AlgebraicGeometry.ProEtale.RationalP1.supported_source_arrow_derived_core` in the
item module. Its source is the second identity of the projective-line rational
adjunction triangle proof.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.ProjectiveSupportedSourceArrowDerived": "11c314f915824e3e7044cbc4826e8e2b7abfa77e"}, "results": {"Sheaf.Paper.ProjectiveSupportedSourceArrow": {"hash": "2e088a355710efb41eb7e156906d602223f675e5", "status": "OK"}}, "seconds": 77, "time": "2026-10-28T10:43:03+0800", "transitive": 0, "version": 1}
```

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
