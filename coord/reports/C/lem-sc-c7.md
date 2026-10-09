# Delivery report: lem-sc-c7

## Files written

- `dag/nodes/sec-proper-base-change/lem-sc-c7.json`: split the proper-curve invariance statement into the three source paragraphs, added paragraph-level sources, recorded LeanSearch/Loogle/Mathlib grep searches, and marked the established cross-unit lemmas as tool uses.
- No new DAG nodes were needed: every proof dependency already exists.

## Attachments

None.

## WANTED

None.

## Corrections and route notes

The imported proof was complete at paragraph level but lacked the stage-1 search records and explicit source metadata. The references to `thm-sc-constant-invariance`, `lem-sc-base-change-curve`, and `lem-sc-artin-schreier-k` are established generic tools from other units; they are recorded in `tool_uses` so the `sk-thm-p1` route remains intact.

## What remains

Nothing for this item.

## Review by C

Reviewed 2026-10-09. The statement and three proof steps agree with the blueprint's C7 route. Each step has an explicit source and non-elementary dependencies; `proof_deps` is unchanged and complete. The three Mathlib search kinds are recorded and no Mathlib declaration states the combined theorem. The cross-unit dependencies are accepted as tool uses by `review_split.py`; `check_dag.py` reports no errors or cycles.
