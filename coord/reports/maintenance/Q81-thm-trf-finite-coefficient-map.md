# Q81: finite coefficient map provider-failure maintenance

Item `thm-trf-finite-coefficient-map`, stage 1, 2026-10-17.

The repeated failures were provider HTTP 429s, followed by loss of the
independent-reader role. Of the sixteen attempts inspected, the first timed out
while preparing the split, the next answered READY after server preflight
passed at `e156ab6ee9`, thirteen completed logs ended in terminal HTTP 429s,
and `.1792197037` was still active. The first failed reader was
`.1792195853`; it read project instructions and then lost the provider stream.
It did not report a DAG, citation, permission or mathematical failure.

The legacy dispatcher used only `last.txt`, which Codex did not write after
these fatal errors. It stored `NOANSWER: `, lost the reader handoff, and issued
fresh author briefs. Some exits between reap and scheduling were also dropped
without accounting for their role. The item is still imported on the server,
with no Q81 delivery ref or return, so earlier Q81 landings of other items do
not complete this one. The retained split still needs independent reading.

Concurrent maintenance has supplied the shared fixes:

- `a1a68055f2`: a scoped Codex entry-point supervisor retries provider 429s,
  resumes known sessions, retains the sandbox and diagnostic, and uses the
  original worker budget. Its atomic CLI entry-point installation applies to
  new launches by the already-running dispatcher.
- `6fb280508f`: dispatcher transport diagnostics, persistent READY handoffs,
  and retained completed worker records for reap.
- `0abb765411`: preserves an interrupted reader's report within the same round.

Q81 maintenance reuses these fixes and supplies the item-specific missing
handoff in `tools/launcher/route-notes/thm-trf-finite-coefficient-map.md`,
deployed at `/home/ubuntu/weil-launcher-nt/route-notes/` on the dispatcher host.
The same handoff is retained as `MAINTENANCE.md` in the Q81 sandbox and linked
from its author report. This reaches a fresh worker even while the old
dispatcher remains loaded. It requires the normal independent reading, current
dry run, and stage-1 delivery; it does not accept or push the mathematics.

The author report is backed up before appending the handoff. New handoff files
have adjacent final `.bak` snapshots. No DAG record, unit binding, Lean source,
claim, failure count or running process is changed by this maintenance.
No compiler or global build is needed. The active worker's existing checks are
not duplicated.

Evidence and the final commit/validation details are in the dispatcher's
maintenance directory:
`/home/ubuntu/weil-launcher-all/maint/Q81-thm-trf-finite-coefficient-map-1792197035/REPORT.md`.
The next worker should use the route note and finish the independent reading.

Validation during maintenance: all 18 server Codex-supervisor regressions and
all 6 dispatcher-reader regressions passed. Run `.1792197037` passed the actual
stage-1 delivery dry run at `d8a896441a` and answered READY. The dispatcher
launched reader `.1792198172` at 08:49:32 +08. The historical failure count
remains 10. This observes recovery to the intended review stage; the item's
delivery and mathematical review remain that reader's responsibility.
