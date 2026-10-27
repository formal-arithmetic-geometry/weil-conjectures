## What changed

The item module now assembles `Construction` from three named intermediate packages. The shared definitions were moved to `ExceptionalFiniteScalarMatesData`; the operation, scalar restriction, and scalar mate existence statements are in separate modules, each with a documented proof plan and a named `sorry`. The item theorem combines their witnesses by a real structure constructor proof. The parent DAG proof was updated to use these three intermediate nodes.

## Proved and sorry left

Closed the original `exceptionalFiniteScalarMates` sorry by decomposition and real assembly. Added the following strictly smaller named statements, each as the whole proof of its theorem:

- `finiteScalarOperation_exists` (`lem-sf-exceptional-finite-scalar-operation`)
- `finiteScalar_exists` (`lem-sf-exceptional-finite-scalar-restriction`)
- `finiteScalarMaps_exists` (`lem-sf-exceptional-finite-scalar-maps`)

The split statements are the operation package, the scalar restriction package, and the scalar mate maps package respectively; none repeats the full target statement.

Reviewer correction (2026-10-28): `finiteScalar_exists` and `finiteScalarMaps_exists` were delivered
without the item's geometric hypotheses (arbitrary `T`, resp. arbitrary `X`, `Y`, `f`, and no `l ≠ p`),
which their cited routes need (the flat-model lemma needs `l` invertible on `T`; the etale compact
scalar coherence theorem needs Noetherian `X`, `Y` and `f` separated of finite type). Both now take the
datum `D`, `l ≠ D.p` and the item's finite-type hypotheses; the item passes them.

## No longer needed

No existing proof dependency was removed. The former monolithic item imports were moved to `ExceptionalFiniteScalarMatesData`, which preserves the public definitions and their required imports. No DAG dependency below the three split packages was pruned.

## Where the brief, the DAG or earlier work was wrong

The original proof plan required a large eight-step construction that could not be completed directly in this item within the available proof surface. The useful reduction is to expose the three independently meaningful packages before assembling `Construction`; the target statement and all existing definitions remain unchanged.

## New nodes

Added `def-sf-exceptional-finite-scalar-mates-data`, `lem-sf-exceptional-finite-scalar-operation`, `lem-sf-exceptional-finite-scalar-restriction`, and `lem-sf-exceptional-finite-scalar-maps`, with corresponding modules and Lean records.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.ExceptionalFiniteScalar": "b4d4cabca6723c5efb9e7a026b6472b757126f02", "Sheaf.Paper.ExceptionalFiniteScalarMaps": "a5057a82c4d641e461cc916b01a653b5f00b6289", "Sheaf.Paper.ExceptionalFiniteScalarMates": "241f3ff70f9b3310ce705a6ea9c04617758088be", "Sheaf.Paper.ExceptionalFiniteScalarMatesData": "ff81628ef42f87fe4cd72688930a2317e512939b", "Sheaf.Paper.ExceptionalFiniteScalarOperation": "90d4003173c85d064fcb7451618f218eeb38f1eb"}, "results": {"Sheaf.Paper.ExceptionalIntegralScalarMates": {"hash": "5350c6dc399af45cba0eb06a2c6e57b36561f3dd", "status": "OK"}}, "seconds": 131, "time": "2026-10-28T01:27:04+0800", "transitive": 0, "version": 1}
```

## Second reading by T6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
