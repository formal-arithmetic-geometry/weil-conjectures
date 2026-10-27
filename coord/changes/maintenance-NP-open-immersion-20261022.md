# NP maintenance: superseded stage-1 claim

Item: `lem-sf-weil-open-immersion-compact-image-extension-by-zero`.

N8 delivered the repaired split at `0fd39b9a684`; independent reviewer
`NT-cc-N8-0fd39b9a6` passed it. Commit `7b12c8e0dd4` landed it at
2026-10-22 04:37:04 UTC. NP acquired a second claim at 04:37:32 UTC
from a stale queue, after N8's claim had closed. The current queue no
longer lists this item, but the dispatcher keeps retrying held stage-1
claims and retains their old stage when queue_stage returns none.

Those workers correctly preserve the reviewed split, and delivery
preflight correctly rejects their unchanged copy. This is completion
bookkeeping, not a mathematical, permission, or provider failure.

Maintenance removed only the superseded NP claim after checking its
original owner and timestamp, the committed passing N8 review,
stage1_completed == True, absence from the current queue, and absence
of a repair note, NP delivery branch, or NP return. The operation and
commit run under SHEAF_LEAD=L-only flock coord/.merge.lock.

Claim backup: `/home/ubuntu/weil-maint-bak/NP-open-immersion-20261022T051557Z/lem-sf-weil-open-immersion-compact-image-extension-by-zero.lock.bak`.
Committed node SHA-256 before cleanup: `ecf9216171edbfc09c3880ebc6b5fef2dccc11ec97c68dd041fb75316c845593`.

The protected dispatcher needs its owner's fix: reconcile held stage-1
claims against the committed completion predicate and live queue before
retrying. When that stage is complete, no repair is owed, and it is no
longer queued, retire the obsolete claim/pending assignment. Recheck
owner and stage so a later-stage claim survives. Continue dispatching
listed unclaimed work as required by the human. Never use failure
counts, caps, throttles, or delays to suppress attempts. Launcher files
and the current tools/claim.py listed-item policy were not changed.

The next worker should preserve N8's split and its two statement-only
dependencies, lem-sf-fixed-pair-derived-forget-comparison and
lem-sf-continuous-adic-proper-base-change-restriction. There is no remaining
stage-1 split for this assignment. The upstream Lean declaration is
still sorry, so this is not a Lean ATTACH or a proof-completion claim.
Only a subsequent explicit repair or later-stage assignment reopens work.

No mathematics, DAG, Lean source, worker sandbox, dispatcher state, or
failure counter changed. No process was signalled; no compiler or
lake build was run.
