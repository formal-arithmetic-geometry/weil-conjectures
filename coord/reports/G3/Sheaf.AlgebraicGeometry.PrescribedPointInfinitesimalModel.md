## What changed

Completed `AlgebraicGeometry.exists_prescribedPoint_infinitesimalModel` in
`Sheaf.AlgebraicGeometry.PrescribedPointInfinitesimalModel`, preserving its statement
and original public imports. Added private, proved helpers for invertible stalk frames,
comparison of the two pullback units, finite-point ideal-power stalk kernels, local jet
representatives, and gluing arbitrary germs on a discrete scheme. Proof imports supply
the existing scalar-extension stalk comparison, closed-immersion kernel calculation,
tensor right exactness, Jacobson topology, and sheaf gluing. No source-library module,
public definition, or consumer changes.

The witnesses are the actual ideal subschemes of the finite closed set and the square
of its vanishing ideal. The jet construction uses precisely the frame selected by
`prescribedPointJet`. Every helper is proved, and empty finite sets are covered by the
same construction and empty-family gluing. The DAG proof now records this argument.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.exists_prescribedPoint_infinitesimalModel`
(node `lem-zl-prescribed-point-infinitesimal-model`).

Original holes: 1. Closed: 1. Added: 0. Split off: 0. Remaining holes in the delivered
module: 0. No new statement is left with `sorry`.

Validation: the complete module compiled through `lcompile.py` in 19.4 seconds with
profiling enabled. The axiom probe for the public theorem returned exactly `propext`,
`Classical.choice`, and `Quot.sound`. Development profiling and the probe command were
removed for the final delivery. The delivery tool recompiles that final file.

## No longer needed

The planned dependencies `lem-weil-pbc-module-iso-on-stalks` and
`lem-weil-pbc-module-stalk-tensor` are not needed by this proof. Section extensionality
replaces the former, and the existing pullback-stalk scalar-extension comparison plus
rank-one frames replaces the latter. Neither is added as a direct proof import. Their DAG dependency
edges are removed for this node; no library module is withdrawn, since they can have
other consumers. The original two public imports remain necessary. No original import
was removed, and no unit-level step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The earlier plan left the finite-point stalk
calculation implicit: isolating one support point on an affine open lets the existing
closed-immersion kernel theorem prove it directly. Discrete-space sheaf gluing also
avoids building separate extensions and then summing them. These are proved private
steps of the same source argument, not new obligations.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
