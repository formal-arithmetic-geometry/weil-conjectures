## What changed

Added `openTensorProjectionComponent`, the adjunction-transposed component of the
normalized open projection. The finite-free, naturality, signed-totalization, K-flat
resolution, and derived-descent work is isolated in one named intermediate theorem,
`openTensorProjection_exists`. The original existence theorem now formally assembles its
natural transformation, obtains the componentwise isomorphism, and proves the displayed
normalization from the component definition. The uniqueness proof remains explicit.

## Proved and sorry left

Closed `SheafOfModules.openImmersionTensor_exists` and retained the proof of
`openImmersionTensor_iso`. One sorry remains: `openTensorProjection_exists`, recorded by
the new node `lemma-weil-pbc-projection-formula-open-piece-projection-existence`.

## No longer needed

The initially proposed separate naturality and component-isomorphism split nodes were
replaced by the single bundled intermediate result; those routes are not part of this
delivery. No imports were removed. The public interface addition is recorded in `coord/changes/open-immersion-tensor-piece.md`.

## Where the brief, the DAG or earlier work was wrong

The earlier split separated natural assembly from componentwise invertibility even though
both are one finite-free and derived-descent construction in the source proof. The route
was consolidated into one strictly simpler intermediate theorem, and the copied existence
node now depends on that theorem.

## New nodes

`lemma-weil-pbc-projection-formula-open-piece-projection-existence` records the bundled
intermediate theorem and its proof dependencies in the sandbox DAG.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
