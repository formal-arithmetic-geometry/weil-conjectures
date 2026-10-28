## What changed

Proved `AlgebraicGeometry.ProEtale.RationalP1.scalar_q_chern_splitting_exists`
in `Sheaf.Paper.RationalP1ScalarChernQSplittingExists`, preserving its signature.
The proof uses the existing completed Chern splitting, realization, scalar-extension
and postcomposition helpers from `DiagonalCompletedChernSplitting`.

Added proof-only imports of `DiagonalFiniteIntegralEndpoint`,
`DiagonalFlatScalarEndpoint`, and `DiagonalClosureLineEndpoint`. The first uses
`import all` to reuse the proved residue-invertibility and integral-line-flatness
helpers. Finite integral extension uses the existing base-scheme integral endpoint.
Rationalization constructs the base endpoint from the uniquely normalized flat
scalar comparison. Closure extension uses the existing closure endpoint at the
bottom finite field. Both coefficient cases finish with the recorded canonical
q pushforward comparison. Local irreducibility attributes keep derived scalar
functors and mates abstract during elaboration. The coefficient cases are split
before unfolding their Chern composites. Endpoint comparisons are selected
directly from their existing normalized existence theorems, avoiding expensive
recursor elaboration. No data is defined from an undetermined existence claim.

Updated the item's DAG proof and dependencies to record these actual base endpoint
constructions. No other existing module, statement, definition, instance, or public
import changes.

Validation: the module compiled through `lcompile.py` with exit code 0, no
warnings, and a reported compile time of 37.1 seconds.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.RationalP1.scalar_q_chern_splitting_exists`
(node `lem-sfb-rational-p1-scalar-q-splitting-existence`).

Added 0 holes and split off 0 statements. No `sorry` remains in the delivered Lean
module. This is a proof from existing declarations, rather than a decomposition.

## No longer needed

None. Both original imports and all original proof dependencies remain needed.
The proof follows the planned route and introduces no new modules or nodes.

## Where the brief, the DAG or earlier work was wrong

The original single proof step omitted the base-scheme line endpoints needed to
transport the complementary summand through scalars. `ScalarCompatibility` has
`lineP` and `lineW`, but no endpoint for the line on Y. The existing finite integral
and closure endpoint theorems provide two comparisons. For rationalization the
integral line is flat, so the existing unique flat scalar comparison supplies the
third comparison with the prescribed ordinary scalar unit. The theorem itself
and all its hypotheses remain unchanged.

The current server queue lists the item as a one-hole stage-3 proof item; there is
no current return, rework row, or build-error record for it.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.RationalP1ScalarChernQSplittingExists": "c3af8bade31bceb61cf4025ed8053420fa5e475d"}, "results": {"Sheaf.Paper.RationalP1ScalarChernQHomologyCriterion": {"hash": "c43987feff460158424ac25935af29d769ecc006", "status": "OK"}}, "seconds": 122, "time": "2026-10-28T10:28:41+0800", "transitive": 0, "version": 1}
```

## Second reading by G5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
