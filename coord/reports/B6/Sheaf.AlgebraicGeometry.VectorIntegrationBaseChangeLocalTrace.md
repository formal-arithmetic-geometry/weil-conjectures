## What changed

Replaced the proof hole in
`AlgebraicGeometry.Etale.vectorIntegration_baseChange_local_trace` with the actual
prefix/counit calculation. The existing theorem signature and public imports are unchanged.
The proof restricts each single-frame prefix along its map to W, pastes the target
prefix with the bundle base-change square, compares the resulting prefixes by a linear
coordinate map, and applies linear trace invariance and affine counit base change.
The supplied arbitrary normalized projective-line data obey base change by
`ordinaryFiniteP1BaseChange_of_normalization`.

Added three proved APIs in new modules:

- `VectorIntegrationBaseCoefficientComposition`: arbitrary-map composition of the
  canonical ordered shifted Tate coefficient transport. This reuses the complete
  general private calculation from `OrderedTateExactOpenComposition`, whose public
  theorem only exposed the nested-open specialization.
- `VectorIntegrationPulledChartTransport`: the Cartesian square and prefix transport
  for one frame pulled along an arbitrary map W to its frame open. The proof generalizes
  the existing restricted-chart coefficient and transport calculations, using the
  arbitrary-map coefficient composition API above.
- `VectorIntegrationCartesianPrefixBaseChange`: pasting an arbitrary Cartesian square
  with a Cartesian affine chart, including its canonical coefficient comparison.
  Naturality, ordinary exchange pasting, inverse square pasting, and coefficient
  composition prove it without any new proof hole.

Added `VectorIntegrationBaseChangeCoordinates` for the remaining equality of scheme
maps. It has no coefficient ring, Tate coefficient, derived category, compact-support
functor, counit, projective-line datum, or trace in its statement. Its proof plan is
pullback of the two free frames, the resulting matrix on the standard global basis,
and the generator formula for the symmetric-algebra base-change map.

All existing-module edits are confined to the assigned module. The new imports there
are private proof imports. No shared definition, existing public signature, instance,
attribute or public import changes, and no existing consumer adaptation is required.

Validation: the server compiled all five sandbox modules, one file at a time in
import order, within the 60-second limit. The final assembly file took 21.2 seconds.
Profiling identified expensive specialized equality rewriting; proved generic
categorical helpers reduced its final kernel check from a timeout to about 1.5 seconds.
The development profiler options were removed before delivery.

## Proved and sorry left

Original holes: 1. Closed in the assigned module: 1,
`AlgebraicGeometry.Etale.vectorIntegration_baseChange_local_trace`.
Added holes: 1,
`AlgebraicGeometry.Etale.vectorIntegration_baseChange_coordinates`
(node `lem-pur-vector-integration-base-change-coordinates`).
Net hole reduction: 0. This delivery is a decomposition, not an unconditional proof
of the original obligation.

The following added declarations are proved, with no new holes in their modules:

- `AlgebraicGeometry.Etale.vectorIntegrationBaseCoefficientPullback_comp`;
- `AlgebraicGeometry.Etale.vectorIntegrationPulledChart_isPullback`;
- `AlgebraicGeometry.Etale.vectorIntegration_pulled_chart_transport`;
- `AlgebraicGeometry.Etale.vectorIntegrationCartesianPrefix_baseChange`.

The remaining statement is strictly the geometric coordinate step. All categorical
pasting, Tate comparison, and counit calculations have complete Lean proofs. It is
not the original trace equality with another name or an additional repackaged hypothesis.
The rank-zero and empty-scheme cases obey the same free-module/generator construction;
no nonempty or positive-rank hypothesis was added.

## No longer needed

No imports were removed and no modules or nodes are withdrawn. No global pruning
is claimed. The proof uses the explicit affine tower counit base-change API rather
than applying `exists_affineSpaceTopTrace`; the original plan's broad compact-support
and finite-twist citations are realized by the explicit exchange and coefficient
composition APIs. Their underlying dependencies remain needed transitively.

## Where the brief, the DAG or earlier work was wrong

The previous node compressed the arbitrary-map frame restrictions, coefficient
composition, and exchange pasting into one step. The existing public restricted-chart
APIs covered nested opens, whereas the assigned theorem has arbitrary maps from W.
The more general coefficient composition calculation already existed privately, so
it was reused to prove the required generalizations. No mathematical contradiction
or target-statement defect was found.

The new coordinate obligation is separated from all trace formalism, and its docstring
and node contain the free-frame/matrix/generator proof in full. This makes a genuine
smaller geometric item instead of repeating the previous local-trace split.

## New nodes

- `lem-pur-vector-integration-base-coefficient-composition`: proved arbitrary-map
  composition of the canonical ordered coefficient pullback.
- `lem-pur-vector-integration-pulled-chart-transport`: proved Cartesian pullback and
  prefix transport of a single frame along an arbitrary scheme map.
- `lem-pur-vector-integration-cartesian-prefix-base-change`: proved generic prefix
  pasting for a Cartesian square and one affine chart.
- `lem-pur-vector-integration-base-change-coordinates`: the sole split-off hole,
  concerning only the equality of two linear scheme charts over W.

The assigned node's proof, proof dependencies, and proof origin now follow the Lean
argument. No change record is needed for a repair to another existing interface:
there is no such repair in this delivery.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.VectorIntegrationBaseChangeCoordinates": "49ea8feee3d8302ddbeeb7e9b80a54fe0d45f9b7", "Sheaf.AlgebraicGeometry.VectorIntegrationBaseChangeLocalTrace": "260a091d3a312e83a5cd87cf32c22e9b85c0d996", "Sheaf.AlgebraicGeometry.VectorIntegrationBaseCoefficientComposition": "6035a64572218a90c4ff58e98437289fa9cb5e66", "Sheaf.AlgebraicGeometry.VectorIntegrationCartesianPrefixBaseChange": "098bb22d5e224173bb8c06636f90a33fdd2f3251", "Sheaf.AlgebraicGeometry.VectorIntegrationPulledChartTransport": "bf5c7752e7916f71a418a122e2ba8adf2a781a7f"}, "results": {"Sheaf.AlgebraicGeometry.VectorIntegrationBaseChangeLocalUnit": {"hash": "8ce2b603a6e61328a24881e84cf65f33cb8cc925", "status": "OK"}}, "seconds": 79, "time": "2026-10-28T10:41:02+0800", "transitive": 0, "version": 1}
```

## Second reading by B6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
