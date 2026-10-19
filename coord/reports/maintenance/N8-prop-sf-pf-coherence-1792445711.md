# N8 maintenance: prop-sf-pf-coherence, 2026-10-20

The failure is an obsolete item-specific brief, not the item mathematics or a
stage-2 compiler failure. The batch-2 dispatcher appends its route note to new
worker prompts without selecting a stage. The installed route note was a
2026-10-17 Q79 stage-1 handoff: it forbade Lean work and prescribed
`python3 /home/ubuntu/weil-launcher-nt/deliver.py Q79 prop-sf-pf-coherence --no-push .`.
That conflicts with the current N8 stage-2 assignment and its authorized sandbox.

## Evidence

- Local dispatcher state `run/N8/state-batch2.json` records stage 2,
  `prop-sf-pf-coherence@new`, five counted failures and the missing-Q79-sandbox
  note. The running worker was started at `1792445717` before this correction.
- All five latest completed logs show the prescribed Q79 call followed by
  `FAILED: no node files under /home/ubuntu/weil-newtargets-sandbox/Q79/prop-sf-pf-coherence/dag/nodes/`:
  `1792440958/log.txt:2018`, `1792441128/log.txt:742`,
  `1792441414/log.txt:3189`, `1792443392/log.txt:10159`,
  `1792445476/log.txt:1553`, under
  `/home/ubuntu/weil-launcher-all/run/N8/prop-sf-pf-coherence.<attempt>/`.
- The stage-1 wrapper discards the `.` argument and derives its sandbox from
  group/item. Supplying a different stage-1 sandbox would still be the wrong
  operation for this stage-2 item. There is no need to change that wrapper.
- Live node `dag/nodes/sec-six-functors/prop-sf-pf-coherence.json` is `split`,
  reviewed pass by `NT-cc-Q75-09de50e71`, Q75, 2026-10-17. Its `lean` and
  `reviewed_lean` records are absent. The stage-1 repair record in
  `coord/repair-notes/prop-sf-pf-coherence.json` is resolved; current Q79
  returns contain no entry for this item.
- Q75 landed the item and its three extracted lemmas in
  `697b9ab6aa7cc1deb30740a051c1223faa5f6856`; the event is recorded at
  `2026-10-17T12:24:59Z` in `coord/deliveries-newtargets.log:7192`.
  `coord/reports/Q75/prop-sf-pf-coherence.md` documents the completed repair.
  The new-targets coordination records joined the live project in `c90ee752c2`.
  No item entry was found in the current `~/cc1/*.log` landing logs.

## Change and validation

Replaced the active local data file
`/home/ubuntu/weil-launcher-all/batch2/route-notes/prop-sf-pf-coherence.md`
and added the identical durable server copy at
`tools/launcher/route-notes/prop-sf-pf-coherence.md`.
The corrected handoff explicitly supersedes the Q79 note and previous BLOCKED
path reports, identifies the accepted Q75 split, and directs N8 to the standard
stage-2 brief, `scompile.py` and `deliver2.py`. The old local note is preserved
as `.maint-N8-1792445711.bak`; new server documents have adjacent initial-content
`.maint-N8-1792445711.bak` snapshots. This report is the second server change.

The dispatcher reads the local note on each new dispatch (`dispatch_all.py:641`);
no restart is needed. The note is below its 12,000-character inclusion limit.
Validate the installed local/server copies byte for byte and confirm the
commit contains exactly these two documentation paths. Commit with
`SHEAF_LEAD=L-only flock coord/.merge.lock` and author
`Bin Wu <844524296@qq.com>`.

No launcher-owned implementation, review or landing tool, configuration,
node record, Lean source, claim, failure counter or sandbox report was changed.
No concurrency setting, admission policy, throttle or pause was introduced.
No compiler or global build was run because this repair changes only the brief.
The obsolete handoff mentions historical provider errors; the five present
failures have the concrete wrong-sandbox diagnostic above. Provider handling
is outside this repair.

## Next worker

Continue stage 2 on the current live node in
`/home/ubuntu/weil-newtargets-stage2-sandbox/N8/prop-sf-pf-coherence`.
The retained report records obsolete routing failures, not a stage-2 packet.
Read the corrected route note and normal brief, state the item and repair
needed dependency interfaces under that brief, compile each delivered file
with `scompile.py`, then dry run and deliver with `deliver2.py N8 prop-sf-pf-coherence`.
Do not recreate Q79's retired sandbox or re-deliver its accepted stage-1 split.
The running worker keeps the prompt it received before this change; future
prompts read the corrected note. It may report one further obsolete failure.
No worker was stopped or restarted. Independent review remains required.

Launcher-owner follow-up: route-note selection should take the assignment's
stage and the current repair/review records into account, so that a resolved
stage-1 handoff cannot override a stage-2 brief. `dispatch_all.py` is protected
and was only read; this maintenance fixes the item-specific data immediately.
