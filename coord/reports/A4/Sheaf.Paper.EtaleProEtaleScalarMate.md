## What changed

Restored the reviewed proof of `Sheaf.Paper.EtaleProEtaleScalarMate` from the prior
T7 delivery and adapted it to the current tree. The three original theorems are now
proved: scalar pullback mate invertibility, bounded-below ambient direct-image mate
invertibility, and the étale/pro-étale scalar-mate equality. The canonical comparison
constructions and their normalization API are shared in `EtaleProEtaleScalarMateData`
to avoid the cube/transposes import cycle. The representative modules retain their
published constructions and add the proved representative-unit equations needed by the
normalization proof. A private `geometric_rep_eq` forwarding lemma is retained in the
item module for existing `import all` consumers.

## Proved and sorry left

Closed the three original holes:

- `AlgebraicGeometry.ProEtale.scalarPullbackReverse_isIso`.
- `AlgebraicGeometry.ProEtale.directImageComparisonAmbient_isIso`.
- `AlgebraicGeometry.ProEtale.etaleProEtale_scalar_mate`.

No new sorry was added. `AlgebraicGeometry.Etale.scalarTensorIso_existsUnique`
remains the pre-existing hole in its dependency and is unchanged in statement.

## No longer needed

The proof uses the existing scalar pullback cube, common counit-transpose theorem,
pro-/étale mate invertibility theorems, and the ambient comparison adjunction. The
relocated data module no longer imports the old direct-image and monoidal proof-only
imports that were only needed before the cycle split. No mathematical DAG node is
withdrawn.

## Where the brief, the DAG or earlier work was wrong

On repair, the packet was rebased against the current `sheaf-dag` tip. The landing failure was caused by a concurrent red-build cleanup removing the unrelated `CoefficientComparisonFiniteReflection` source from that baseline; it is not imported by this item. The repair preserves the current baseline dependencies and records the refreshed proof-origin metadata below.

The previous reviewed landing was removed by the merge queue because a downstream
`EtaleOpenScalarCoherence` proof used the private `geometric_rep_eq` compatibility lemma
that the refactor had removed. This delivery restores that lemma without changing any
public signature or construction. The prior proof route itself remains valid and follows
the recorded cube and counit-transpose steps.

The complete packet and the unchanged `Sheaf.SixFunctors.EtaleOpenScalarCoherence`
regression consumer compiled successfully (exit code zero).

Change record: `coord/changes/T7-etale-proetale-scalar-mate-data.md`.

## New nodes

`lem-sfb-proetale-scalar-pullback-mate-invertible` and
`lem-sfb-scalar-site-comparison-normalized-data` are already present in the DAG and are restored with their Lean modules
by this delivery. Their declarations are proved in the supplied helper modules.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
