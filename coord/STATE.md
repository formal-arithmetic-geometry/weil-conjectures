# STATE

The current state of the run. Only the launcher and the maintainer write here, each in its own section; everyone else reads it. Each section is rewritten to the present state, never appended to. Questions for the human go to `coord/HUMAN.md`, history to `coord/ledger.md`.

## Stages open

Written by the launcher at the start (`1-dag`), then kept current by the maintainer: every stage that has open or waiting items, since the stages overlap (`roles/maintainer.md` §6).

`1-dag`, the only open stage (SETUP.md, requirements of 2026-10-09). The 21 cycles were removed on 2026-10-09. The stage-1 queue (`tools/dag_queue.py`, adapted the same day) is the item set of SETUP.md: 1870 items at the start of the run (1787 with no Lean, 55 resting on a sorry, 23 with a sorry of their own, 5 partly closed), 319 nodes finished (closed on slopmaster2). `coord/queue.md` lists them nearest to the target first; the three stage-2 lines it also prints are not claimable, since stage 2 is not open. Workers follow `coord/brief-stage1.md`. Progress is in `coord/ledger.md`, one line per batch.

**Pilot numbers after the first batch (2026-10-09).** Ten workers started at 05:53 UTC; the account's 5-hour session limit stopped the session at about 06:55 UTC with 5 items delivered, 2 more written but unreported, and 7 unfinished (their work lost or partial), so one batch of 10 xhigh fable workers plus the lead consumes roughly one 5-hour window per hour of running. A delivered item took 9.5–14 minutes of wall time (575, 563, 708, 721, 852 s) and 119k–192k worker tokens (119k, 131k, 162k, 169k, 192k), the heavier statements being the slower ones; each item produced 1–5 new nodes, about half of them Mathlib leaves. What the workers got wrong: none was wrong mathematically on review; two could not read the PDFs (no `pdftotext` on the machine, now installed) and wrote the proof as an agent's where Milne or Deligne is in `literature/`; one refused to run the review script because the brief forbade `git` (brief fixed); one that died mid-item left its node citing two nodes it had not written yet (brief now says to write new nodes first); all left claims inside definitions as the source wrote them and reported them rather than moving them out, which is right for stage 1.

## Plan

Written by the launcher: the names of the sessions of the project.

One session, group `L`: the maintainer and the only lead, started 2026-10-09. It gives items to at most 10 workers at a time (sub-agents, model fable, effort xhigh), each splitting one node by one level, reviews each delivery, and commits after every batch.
