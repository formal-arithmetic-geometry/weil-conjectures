## What changed

The scalar Q splitting proof now assembles a two-sided inverse from two explicit
intermediate transport statements. The item module imports the right-inverse and
left-inverse modules and performs the categorical uniqueness calculation for their
inverse candidates. The two new modules state the corresponding one-sided inverse
obligations and preserve the original scalar map and hypotheses.

## Proved and sorry left

Proved `AlgebraicGeometry.ProEtale.RationalP1.scalar_q_chern_splitting`.
The delivery adds the two split-off obligations, each with one `sorry`:
`scalar_q_chern_right_inverse` (node
`lem-sfb-rational-p1-scalar-q-right-inverse`) and
`scalar_q_chern_left_inverse` (node
`lem-sfb-rational-p1-scalar-q-left-inverse`).

## No longer needed

None. The original proof import of `Sheaf.Paper.RationalP1ScalarChernMaps`
remains needed by the item and by both split-off statements.

## Where the brief, the DAG or earlier work was wrong

The original node treated transport of the completed splitting to the explicit
scalar map as one indivisible proof step. The delivery exposes its two one-sided
inverse equations as separate lower obligations; the target node's route is
updated accordingly. No target statement or definition was changed.

## New nodes

`lem-sfb-rational-p1-scalar-q-right-inverse` and
`lem-sfb-rational-p1-scalar-q-left-inverse` are new nodes in the
`sk-prop-p1-adjunction-rational` unit. Each records the corresponding one-sided
inverse transport statement and its source in the rational projective-line
triangle proof.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.RationalP1ScalarChernQLeftInverse": "614350ad83d44f3d08e932eab39b07c7e78d9bc4", "Sheaf.Paper.RationalP1ScalarChernQRightInverse": "d69b443d7c2ea32fa7ffe04c4f9b1e4af12d7dba", "Sheaf.Paper.RationalP1ScalarChernQSplitting": "317550e29fa825425c4a0cc98ef061193ff9af7d"}, "results": {"Sheaf.Paper.RationalP1ScalarChernSplittings": {"hash": "cb8089e862807e3e960ab382934c4b655948d9e8", "status": "OK"}}, "seconds": 35, "time": "2026-10-28T04:26:57+0800", "transitive": 0, "version": 1}
```

## Second reading by J3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
