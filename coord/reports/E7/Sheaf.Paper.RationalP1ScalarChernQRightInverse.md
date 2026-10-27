## What changed

Filled `scalar_q_chern_right_inverse` by reducing it to a homological criterion for the scalar q unit/Chern biproduct. The proof includes a proved generic derived-category criterion that a biproduct map is an isomorphism from the homology concentration and component isomorphisms, then takes the inverse. Added `Sheaf.Paper.RationalP1ScalarChernQHomologyCriterion` containing the remaining geometric transport statement as a named split-off theorem.

## Proved and sorry left

The `scalar_q_chern_right_inverse` sorry is closed. The new theorem `scalar_q_chern_homology_criterion` remains as one sorry, with node `lem-sfb-rational-p1-scalar-q-homology-criterion`.

## No longer needed

The original dependency `lem-sfb-diagonal-trace-twisted-splitting-components` is no longer imported by the item proof directly; it is retained as a dependency of the split-off homological criterion. No other planned imports were needed.

## Where the brief, the DAG or earlier work was wrong

The original one-step route omitted the intermediate homological concentration and invertibility statement needed to assemble the categorical inverse. The item is therefore reduced through the new strictly simpler criterion.

## New nodes

`lem-sfb-rational-p1-scalar-q-homology-criterion` is stated in `lean/Sheaf/Paper/RationalP1ScalarChernQHomologyCriterion.lean` and records the remaining geometric transport and projective-line homology calculation.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.RationalP1ScalarChernQHomologyCriterion": "5e068c2c2fac44c6667563c7bb637499541eae61", "Sheaf.Paper.RationalP1ScalarChernQRightInverse": "f9ee6136653c9e849e032e4aa625e104a8c70851"}, "results": {"Sheaf.Paper.RationalP1ScalarChernQSplitting": {"hash": "317550e29fa825425c4a0cc98ef061193ff9af7d", "status": "OK"}}, "seconds": 101, "time": "2026-10-28T05:11:39+0800", "transitive": 0, "version": 1}
```

## Second reading by E7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
