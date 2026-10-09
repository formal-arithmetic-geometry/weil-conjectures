# STATE

The current state of the run. Only the launcher and the maintainer write here, each in its own section; everyone else reads it. Each section is rewritten to the present state, never appended to. Questions for the human go to `coord/HUMAN.md`, history to `coord/ledger.md`.

## Stages open

Written by the launcher at the start (`1-dag`), then kept current by the maintainer: every stage that has open or waiting items, since the stages overlap (`roles/maintainer.md` §6).

`1-dag`, the only open stage (SETUP.md, requirements of 2026-10-09). The 21 cycles were removed on 2026-10-09. The stage-1 queue (`tools/dag_queue.py`, adapted the same day) is the item set of SETUP.md: 1870 items at the start of the run (1787 with no Lean, 55 resting on a sorry, 23 with a sorry of their own, 5 partly closed), 319 nodes finished (closed on slopmaster2). `coord/queue.md` lists them nearest to the target first; the three stage-2 lines it also prints are not claimable, since stage 2 is not open. Workers follow `coord/brief-stage1.md`. Progress is in `coord/ledger.md`, one line per batch.

## Plan

Written by the launcher: the names of the sessions of the project.

One session, group `L`: the maintainer and the only lead, started 2026-10-09. It gives items to at most 10 workers at a time (sub-agents, model fable, effort xhigh), each splitting one node by one level, reviews each delivery, and commits after every batch.
