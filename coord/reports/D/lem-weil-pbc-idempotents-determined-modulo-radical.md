# Stage 1 report: `lem-weil-pbc-idempotents-determined-modulo-radical`

## Review by D

The item is split along Stacks Project, Lemma Tag 09XF. The statement is unchanged. Its proof has two complete steps: localize at each maximal ideal and use the fact that a local ring has only the idempotents 0 and 1; then use the annihilator argument to deduce equality from equality in every maximal localization. Both steps are marked elementary and cite the Stacks source and Tag 00HN. The recorded LeanSearch, LeanFinder, Loogle, and Mathlib grep searches found no Jacobson-radical idempotent uniqueness theorem; Mathlib only supplies the nilpotent-kernel variant, so the item remains a DAG statement rather than a Mathlib leaf.

Files written:

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-idempotents-determined-modulo-radical.json` — existing statement node, now `status: split`; no new nodes.
- `coord/reports/D/lem-weil-pbc-idempotents-determined-modulo-radical.md` — this report.

Attachments: none.

WANTED: none; `literature/stacks-project/more-algebra.tex` is already cited by the node.

No statement or blueprint error was found. No work remains for this stage-1 split.

Validation: `python3 tools/check_dag.py` passed with 0 errors and 0 cycles; `python3 tools/review_split.py lem-weil-pbc-idempotents-determined-modulo-radical` passed with 0 new nodes.
