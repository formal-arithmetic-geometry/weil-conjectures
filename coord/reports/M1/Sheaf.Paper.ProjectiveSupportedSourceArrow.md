## What changed

Closed the `supported_source_arrow` hole by unfolding the normalized supported source
map and applying a new derived-unit evaluation lemma. Added
`Sheaf.Paper.ProjectiveSupportedSourceArrowDerived`, whose statement isolates the
canonical right-derived single comparison before cancellation. The item imports
this proof-only module; all imports remain limited to the project modules needed by
the statement and the reduction.

## Proved and sorry left

The original theorem `AlgebraicGeometry.ProEtale.RationalP1.supported_source_arrow`
is proved. One strictly simpler theorem remains as a named split:
`AlgebraicGeometry.ProEtale.RationalP1.supported_source_arrow_derived` in
`Sheaf.Paper.ProjectiveSupportedSourceArrowDerived`, node
`lem-sfb-projective-supported-source-arrow-derived`. No definition contains a
`sorry`.

## No longer needed

No existing mathematical import or DAG dependency is withdrawn. The proof uses the
new derived-unit evaluation node and the normalized source definition; the other
original proof-plan citations are recorded on the new node as its dependencies.
The exploratory `Checks` module was removed from the delivery sandbox.

## Where the brief, the DAG or earlier work was wrong

The original one-step proof plan did not expose the canonical right-derived
single-comparison evaluation as a separately stated Lean theorem. Splitting that
strictly earlier evaluation step makes the remaining cancellation argument a direct
unfolding and application while preserving the unit route and the target statement.

## New nodes

`lem-sfb-projective-supported-source-arrow-derived` states the canonical
right-derived unit evaluation on the normalized supported source before cancellation.
Its source is the second identity in
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-prop-p1-adjunction-rational/sk-prop-p1-adjunction-rational-triangle.proof.md`.
The statement was checked against the existing `Diagram.support₂`,
`secondDiagramPushIso`, `supportedUnitIso`, and `pushSectionIso` declarations; no
Mathlib theorem matches this project-specific identity.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.ProjectiveSupportedSourceArrow": "2e088a355710efb41eb7e156906d602223f675e5", "Sheaf.Paper.ProjectiveSupportedSourceArrowDerived": "161b6d47efbd3561ff8db582df2bf3d8c6e9a633"}, "results": {}, "time": "2026-10-28T09:30:31+0800", "transitive": 0, "version": 1}
```

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
