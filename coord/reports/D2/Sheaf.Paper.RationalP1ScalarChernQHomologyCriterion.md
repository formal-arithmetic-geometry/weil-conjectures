## What changed

Proved `scalar_q_chern_homology_criterion` in
`lean/Sheaf/Paper/RationalP1ScalarChernQHomologyCriterion.lean`. The proof uses the
T-structure concentration of the unit and shifted scalar line, biproduct homology
identities, the infinity-section split-mono argument for the q unit, and a new
geometric complementary-component statement. Added
`Sheaf.Paper.RationalP1ScalarChernQSplittingExists` for that lower statement and
imported it from the criterion module.

## Proved and sorry left

Closed the item's one `sorry`, the theorem
`AlgebraicGeometry.ProEtale.RationalP1.scalar_q_chern_homology_criterion`.
Added one strictly simpler split-off theorem,
`AlgebraicGeometry.ProEtale.RationalP1.scalar_q_chern_splitting_exists`, whose
proof remains `sorry` and is recorded by node
`lem-sfb-rational-p1-scalar-q-splitting-existence`.

## No longer needed

The item proof no longer directly follows the original geometric proof step
through `lem-sfb-diagonal-trace-twisted-splitting-components`; that transport is
encapsulated by the split-off complementary-component theorem. The criterion
module therefore does not import `Sheaf.Paper.DiagonalCompletedChernSplitting`
directly. No target statement or existing declaration was changed.

## Where the brief, the DAG or earlier work was wrong

The DAG's single geometric proof step combines the q complementary splitting
transport with the homological argument. Existing q scalar compatibility records
supply the unit and projective-line endpoints used by `scalarQChern`, but do not
supply the base line endpoint needed to construct the complementary shifted-line
map in the criterion. The geometric transport is therefore recorded as one
strictly simpler lower theorem so the homological argument can be completed from
a named statement.

## New nodes

`lem-sfb-rational-p1-scalar-q-splitting-existence` is stated in
`lean/Sheaf/Paper/RationalP1ScalarChernQSplittingExists.lean`; its proof is the
normalized completed q splitting transported through realization, scalar
compatibilities, and the canonical q pushforward comparison. It has no separate
change record because it is a new statement module.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.RationalP1ScalarChernQHomologyCriterion": "c43987feff460158424ac25935af29d769ecc006", "Sheaf.Paper.RationalP1ScalarChernQSplittingExists": "1b42633396a30655b5d116e72ca389d1c597ec42"}, "results": {"Sheaf.Paper.RationalP1ScalarChernQRightInverse": {"hash": "f9ee6136653c9e849e032e4aa625e104a8c70851", "status": "OK"}}, "seconds": 31, "time": "2026-10-28T08:14:19+0800", "transitive": 0, "version": 1}
```

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
