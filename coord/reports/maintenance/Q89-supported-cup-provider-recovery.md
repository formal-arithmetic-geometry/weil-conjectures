# Q89 maintenance: supported cup provider interruptions

The ten failures counted under `def-pur-supported-cup@` were all Codex HTTP 429
interruptions, not mathematical or Lean failures. The final logs under
`/home/ubuntu/weil-launcher-all/run/Q89/def-pur-supported-cup.*` contain the
terminal provider error and no `last.txt`. Seven startup attempts did essentially
no item work. Longer attempts retained useful files in
`/home/ubuntu/weil-newtargets-sandbox/Q89/def-pur-supported-cup` but lost session
context when restarted. The five-failure maintenance attempt also died with 429.
The old dispatcher read only `last.txt`, so its note became empty `NOANSWER: `.

The original C4/E4 literature return is a separate, real review obligation. The
server item is unsplit and the return is still open. The 2026-10-16 N3 delivery
log is historical and does not mean that this reopened repair is done.

Concurrent maintenance supplied the shared transport fix while this audit was
running: server commit `6fb280508f` preserves reader handoffs and retries
transient worker failures; the installed `codex_retry.py` supervises dispatched
CLI calls, resumes exact persisted sessions, keeps their budget and sandbox,
and emits a diagnostic when recovery is exhausted. Follow-up `a5ae0952c3` covers
explicit dispatcher resumes. These changes have their own adjacent backups.
The local CLI symlink now points to that supervisor; existing dispatcher and
worker processes were not stopped by this maintenance task. Additional adaptive
admission changes observed on disk are concurrent work, not a claim that the
old running dispatcher has reloaded them.

This maintenance adds the item-specific route note at
`tools/launcher/route-notes/def-pur-supported-cup.md` (installed locally at
`/home/ubuntu/weil-launcher-nt/route-notes/def-pur-supported-cup.md`) and adds an
infrastructure handoff to `coord/repair-notes/def-pur-supported-cup.json`, preserving
its state, original note and original C4/E4 reason. The route note tells retries
to retain the saved packet, use the correct author/reader role, begin with the
required dry run, and use no Lean compiler in stage 1. No mathematical node or
Lean file is changed by maintenance.

Validation: 18 server Codex recovery tests pass, including temporary throttling,
exact-session resume, missing-session fallback, deadline bounds, cancellation,
quota/authentication exclusion and no replay after a real answer. Seventeen
local focused transport/classification/no-answer tests also pass. A wider local
handoff test initially exposed concurrent fixture drift (`stage1_handoff` was
missing from its extracted-AST test namespace); this is separate from runtime
behavior and is not used as evidence for that handoff path here.

Operational evidence: run `1792196923` completed two server dry runs, finally
`OK (not pushed) ... at a1d795acd8`, then READY at 08:40:14 Asia/Shanghai on
2026-10-17. The dispatcher launched an independent reader in run `1792197614`.
That reader has appended its audit and is validating/delivering. No dry-run
commit is claimed to be landed. The normal independent review still decides
the mathematical repair.

Files changed by this task have adjacent `.maint-Q89-provider-1792196921.bak`
backups. The server installation, exact staging and commit use
`SHEAF_LEAD=L-only`, `flock coord/.merge.lock` and
`Bin Wu <844524296@qq.com>`. The local maintenance `REPORT.md` records the resulting
commit and final observed worker state. No Lean compilation or lake build was
needed, no failure counter was edited, and no process was killed.
