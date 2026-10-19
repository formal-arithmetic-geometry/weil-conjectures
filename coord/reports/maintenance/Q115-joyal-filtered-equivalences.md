# Q115 maintenance: lem-coef-joyal-filtered-equivalences

The ten counted failures were infrastructure interruptions. Twelve completed
attempt directories are present (the old dispatcher could lose an ended worker
between `reap()` and `work()`, so the directory count exceeded `tries`). Every
completed log through attempt `1792196979` ends in Codex HTTP 429 retry exhaustion
and has no `last.txt`. The first worker reached a successful dry run and then a
successful compile of its expanded docstring/imports; it lost the API session
while waiting on its final dry run. The maintenance attempt at `1792196319` also
died with HTTP 429. No Q115 stage-2 return or landing rejection was found.

Cause: the dispatcher read only a missing final-answer file, recorded a blank
`NOANSWER:`, and repeatedly launched a fresh authoring session. Failure totals
are observations, not dispatch cutoffs. The shared transport repair, committed
concurrently as `6fb280508f56f3ab9401bdc8651a572b0e6bee43`, recovers the terminal
diagnostic, delays transient retries within the worker budget, and retains the
reader handoff. Follow-up reader-report repair `0abb765411` preserves an
interrupted reader's report in the same delivery round. This maintenance verified
the transport classifier against all twelve actual completed item logs and ran
the server's transport/classification/stage-2-handoff suites: 18 tests passed.

This item's repair adds
`tools/launcher/route-notes/lem-coef-joyal-filtered-equivalences.md` and installs it
at `/home/ubuntu/weil-launcher-nt/route-notes/lem-coef-joyal-filtered-equivalences.md`.
The dispatcher reads that directory for future authoring briefs. The note directs
the worker to the saved packet and the precise remaining dry-run/second-reader
path. It does not waive any self-check, compile or independent reading.

The packet's Lean, DAG record, worker report, dispatcher state, failure totals and
claims were not edited. An authoring worker was already active and running the
dry run during maintenance; no duplicate delivery was started. No process was
stopped and no Lean build was run. Backups for new maintained paths record that
the path was previously absent; existing paths, if present at installation, are
copied verbatim before writing. The installation and commit run under
`coord/.merge.lock`, with `SHEAF_LEAD=L-only` and
`Bin Wu <844524296@qq.com>`.

Detailed evidence and the final local report are in
`/home/ubuntu/weil-launcher-all/maint/Q115-lem-coef-joyal-filtered-equivalences-1792197004/`.
The provider's precise reason for HTTP 429 is not exposed in the logs. The
repair handles the observed interruption; it cannot guarantee provider capacity.
The existing dispatcher must load committed source changes through its normal
restart lifecycle; the route note is read dynamically on each later launch.
