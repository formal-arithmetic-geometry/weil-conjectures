# STATE

The current state of the run. Only the launcher and the maintainer write here, each in its own section; everyone else reads it. Each section is rewritten to the present state, never appended to. Questions for the human go to `coord/HUMAN.md`, history to `coord/ledger.md`.

## Stages open

Written by the launcher at the start (`1-dag`), then kept current by the maintainer: every stage that has open or waiting items, since the stages overlap (`roles/maintainer.md` §6).

`1-dag`, the only open stage (SETUP.md, requirements of 2026-10-09). The 21 cycles were removed on 2026-10-09. The stage-1 queue (`tools/dag_queue.py`, adapted the same day) is the item set of SETUP.md: 1870 items at the start of the run (1787 with no Lean, 55 resting on a sorry, 23 with a sorry of their own, 5 partly closed), 319 nodes finished (closed on slopmaster2). `coord/queue.md` lists them nearest to the target first; the three stage-2 lines it also prints are not claimable, since stage 2 is not open. Workers follow `coord/brief-stage1.md`. Progress is in `coord/ledger.md`, one line per batch.

**Pilot numbers, effort `xhigh` (batches 1–2, 2026-10-09, 05:53–07:20 UTC).** Two accounts hit their 5-hour session limits: the first after about an hour with 10 workers running, the second after 16 minutes (it had been used elsewhere). 11 items were delivered and passed review: 9 with a report, 2 found complete on disk after their worker died; 12 workers died mid-item, 7 of them leaving nothing usable. Per delivered item: 9.5–14 minutes of wall time (563–852 s, median ~720 s) and 119k–268k worker tokens (median ~170k); 0–6 new nodes per item (median 2), about half of them Mathlib leaves. The review rejected nothing mathematically; what it had to correct or note: two workers could not read the PDFs (no `pdftotext`; installed since) and wrote the proof as an agent's; one refused the review script because the brief forbade `git` (brief fixed); one died leaving its item citing nodes it had not written (brief now says new nodes first); one removed a pointer clause from a definition's statement (accepted, the slopmaster2 text has no such clause); claims inside definitions were kept as the source wrote them and reported.

**Pilot numbers, effort `medium` (batch 3, started 07:32 UTC, human's decision in SETUP.md).** To be filled in as the items come back: wall time and tokens per item, new nodes per item, what the review rejected or corrected.

## Plan

Written by the launcher: the names of the sessions of the project.

One session, group `L`: the maintainer and the only lead, started 2026-10-09. It gives items to at most 10 workers at a time (sub-agents, model fable, effort xhigh), each splitting one node by one level, reviews each delivery, and commits after every batch.
