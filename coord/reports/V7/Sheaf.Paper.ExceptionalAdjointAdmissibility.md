## What changed

Closed the original `exceptionalFiniteSupportExtensionMap_isIso` hole. The proof transports
through the intrinsic finite-coefficient realization, uses conservative restriction of
scalars, and reduces each component to a constant-coefficient proper projection. Added the
componentwise intermediate theorem, the constant-support projection module, and the
arrow-level scalar-mate normalization module. Updated the item node with the actual proof
route and three new DAG nodes.

## Proved and sorry left

The original declaration `WeilConjectures.exceptionalFiniteSupportExtensionMap_isIso` is
proved (1 of 1 original sorries). Three genuinely separate intermediate results remain:

- `WeilConjectures.exceptionalFiniteSupportExtensionMap_component_after_restriction_isIso`
  in `ExceptionalAdjointAdmissibility.lean`;
- `AlgebraicGeometry.ProEtale.isIso_constantSupportProjection` in
  `ProEtaleConstantSupportProjection.lean`;
- `WeilConjectures.supportScalarMate_projection_arrowIso` in
  `SupportScalarProjectionNormalization.lean`.

These are the coefficientwise generation, constant-projection, and scalar-mate
normalization results used by the completed top-level proof.

## No longer needed

None. All imports retained by the proof are used. No existing DAG dependency or module was
pruned. The forced public import is recorded in `coord/changes/exceptional-support-import.md`.

## Where the brief, the DAG or earlier work was wrong

The original proof plan omitted the intrinsic-realization transport and the arrow-level
normalization needed to connect the supplied scalar mate to the proper projection map. The
DAG therefore had no declarations for those two steps; they are recorded as new nodes. The
constant-projection step also requires an explicit noetherian coefficient hypothesis because
that is the hypothesis of the available module-generation infrastructure.

## New nodes

- `lem-exc-proetale-constant-support-projection` —
  `dag/nodes/sec-smooth-purity/lem-exc-proetale-constant-support-projection.json`.
- `lem-exc-support-scalar-projection-normalization` —
  `dag/nodes/sec-smooth-purity/lem-exc-support-scalar-projection-normalization.json`.
- `lem-exc-support-component-after-restriction` —
  `dag/nodes/sec-smooth-purity/lem-exc-support-component-after-restriction.json`.

## Second reading by V7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
