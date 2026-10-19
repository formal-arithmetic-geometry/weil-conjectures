# Q32 classical continuity-map maintenance, 2026-10-17

The short NOANSWER attempts for det-pe-classical-definition-continuity-map
terminated in Codex HTTP 429 Too Many Requests. The scoped runner recovery in
commit a1a68055f2 is deployed through the Codex entry point; its eleven fake-CLI
regressions pass. It retries inside the existing worker budget and retains the
exact interrupted session. This maintenance does not add another retry layer,
change the configured model, gate dispatch on failure counts, or stop workers.

The first long attempt also found a stale lean.statement signature. The active
worker has corrected that metadata and its saved module compiles within four
seconds per file using the prescribed 60-second single-file checks. No Lean or
mathematical statement is changed by this maintenance.

A current dry run found an unrelated generated coord/blueprint-index.tsv already
staged in the disposable delivery worktree. Adding only packet paths leaves
pre-staged paths in the index. deliver2.py now resets that private index to HEAD
before staging its explicit packet list and checks the staged paths against it.
The reset preserves worktree contents. It never runs in the shared checkout or
worker sandbox. The stage-2 server preflight remains unchanged.

The real-Git regression pre-stages a generated file, stages a packet, and checks
that only the packet is staged and both files' contents survive. A second test
checks that unexpected staging is rejected. The item route note tells the next
worker to resume the saved packet, dry-run it first, and preserve the independent
second-reader handoff.

Local deployment: /home/ubuntu/weil-launcher-nt/deliver2.py and its sibling test
and route-notes/det-pe-classical-definition-continuity-map.md. Tracked copies:
tools/launcher/deliver2.py, tools/launcher/test_deliver2_packet.py and the same
route note under tools/launcher/route-notes/. Backups end in
.maint-Q32-packet-1792196976.bak. Commit under coord/.merge.lock as Bin Wu.
