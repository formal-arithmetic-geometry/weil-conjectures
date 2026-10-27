## What changed

The original factorization theorem is proved by composing two strictly smaller
interfaces. `DiagonalTraceFiniteAdjunctionSupported` constructs the common finite
operation and proves its equation on all supported completed arrows.
`DiagonalTraceFiniteAdjunctionGeometric` proves the geometric adjunction equation
for an operation with that supported normalization. The item module imports both
proof-only modules and packages their common witness and equations.

## Proved and sorry left

`diagonalTrace_finiteAdjunction_factorization` is closed in the item module by a
complete Lean proof. Two split-off sorries remain, one in each new theorem:

- `diagonalTrace_finiteAdjunction_supported` in
  `lem-sfb-diagonal-trace-finite-adjunction-supported`;
- `diagonalTrace_finiteAdjunction_geometric` in
  `lem-sfb-diagonal-trace-finite-adjunction-geometric`.

No definition contains a sorry. This is a decomposition of one upper proof hole
into the supported-arrow construction and the independent geometric-arrow
calculation; the combining proof is complete.

## No longer needed

No existing public import was removed. The parent proof now uses the two new
proof-only imports and no longer directly needs its former generic proof-dependency
list in the parent node; those dependencies remain the stated inputs of the two
split nodes. No unit-level statement was bypassed and no existing module was
withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original proof prose bundled two independent normalizations under one
existential witness. The supported-arrow equation fixes the operation, while the
geometric equation is a separate adjunction calculation. Splitting at that
mathematical boundary makes the parent proof a real combination of smaller
statements. No target statement was changed or weakened.

## New nodes

`lem-sfb-diagonal-trace-finite-adjunction-supported` records construction and
normalization on supported arrows. `lem-sfb-diagonal-trace-finite-adjunction-geometric`
records the geometric hom-equivalence calculation for a supported-normalized
operation. Both are strictly smaller than the parent existential statement and
have complete source and proof descriptions in their docstrings and node files.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.DiagonalTraceFiniteAdjunctionFactorization": "a79f7579df4f7ee9a4ff447200c37a9af4160a6b", "Sheaf.Paper.DiagonalTraceFiniteAdjunctionGeometric": "bbf1a7163aa6c6cedfd3856b682c556a2432b08c", "Sheaf.Paper.DiagonalTraceFiniteAdjunctionSupported": "749a150fa7d8167661218ec7692ab9704df5539d"}, "results": {}, "time": "2026-10-28T00:10:48+0800", "transitive": 0, "version": 1}
```

## Second reading by R5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
