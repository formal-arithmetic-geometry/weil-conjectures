# NP integral compact-support preflight recovery, 2026-10-21

Item: `lem-sf-integral-compact-support-constructible`, stage 1.
Dispatcher key: `lem-sf-integral-compact-support-constructible@100b8fa83`.

Repeated failures came from an inherited 18-node DAG cycle. Commit
`35763188dc` replaced the foundational finite/integral direct-image Lean owner
with the common-stage owner; `8ae757b401` attached the upper construction's
proof dependencies. Those dependencies reach integral constructibility and
compact support, whose finite/integral inputs use the foundational definition.
The worker correctly could not edit the intervening existing records.

Concurrent maintenance N0 landed the cause repair in
`2c7a6bc6aa139c3610900aa287ae2710ea9033c2` while NP maintenance was diagnosing
the same SCC. It restores `def-weil-derived-direct-image` to
`Sheaf.Paper.SfDerivedDirectImage` and moves the existing upper interface,
proof and provenance to `def-weil-common-stage-derived-direct-image`, with a
common-stage consumer reference. No Lean source or mathematical proof changed.

NP independently verified that substituting the pre-repair definition recreates
the 18-node SCC and that the current definition removes it. The server's global
`tools/check_dag.py --cycles` still reports unrelated baseline findings; it no
longer reports this SCC. The normal item command
`python3 /home/ubuntu/weil-launcher-all/batch2/deliver.py NP lem-sf-integral-compact-support-constructible --no-push`
exited 0: `OK (not pushed) deliver/NP/lem-sf-integral-compact-support-constructible
at 9754a626385: preflight passed`. The tool saved its durable handoff receipt.

The existing four-child split, seven-step 2621-character parent assembly,
23 citations and search records remain in the NP sandbox. Maintenance changed
no sandbox node or report, and pushed no item branch. The item's launcher route
note now identifies the repaired base and successful dry run; its prior version
is backed up as `.maint-NP-1792553934.bak`. The next worker should retain that
work, refresh main and follow the normal dry-run/delivery/review path. Older
BLOCKED entries describe the obsolete base. No launcher tool or dispatch state
was modified; no concurrency or admission setting was added.
