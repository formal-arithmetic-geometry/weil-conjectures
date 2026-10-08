# STATE

The current state of the run. Only the launcher and the maintainer write here, each in its own section; everyone else reads it. Each section is rewritten to the present state, never appended to. Questions for the human go to `coord/HUMAN.md`, history to `coord/ledger.md`.

## Stages open

Written by the launcher at the start (`1-dag`), then kept current by the maintainer: every stage that has open or waiting items, since the stages overlap (`roles/maintainer.md` §6).

`1-dag`. The DAG was imported from the blueprint on 2026-10-08 (`tools/import_blueprint.py`; counts in `dag/import_report.json`). `tools/dag_queue.py summary` on that date: 2320 nodes, 7 Mathlib leaves, 1 target, 16 not reached; stage 1 open: 91 nodes. `tools/check_dag.py` reports 21 dependency cycles (117 nodes), which stage 1 has to resolve before the graph meets `stages/1-dag.md` §6. No maintainer or lead session has been started.

## Plan

Written by the launcher: the names of the sessions of the project.
