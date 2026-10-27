# commonStagePullbackCompComponent_naturality_ofHom

## Reason

The parent naturality proof proceeds by induction on the quotient pair category.
Its finite common-stage representative calculation is a distinct, strictly smaller
step and is recorded as a public intermediate theorem for a follow-up worker.

## Old

The item module had no explicit representative-stage declaration; the parent
naturality theorem was a single `sorry`.

## New

The item module adds
`commonStagePullbackCompComponent_naturality_ofHom`, which restricts the naturality
square to an arrow represented at a fixed coefficient stage. The parent theorem is
proved by `StageSystem.PairCategory.hom_induction` from this helper. The helper's
proof remains `sorry` and has its own DAG node.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.WeilIndSheafCategory | unclaimed | Sees the added helper declaration; existing imports and signatures remain compatible. |

## Status

landed 20261027T234050-L-4179754 2026-10-27 (merge of deliver/M1/Sheaf.Paper.CommonStagePullbackCompNaturality)
