# NQ: completed polynomial-model base-change split assigned again

The stage-1 failures are stale assignment records. Q49's accepted split is
commit cd375ae75d72235f62935120ea066b65eefe3973, reviewed PASS by
NT-cc-Q49-a0ab8e59a, merged at 2026-10-24T01:38:57Z. NQ took a new claim
at 01:39:48Z. The node is split/reviewed/pass; dag_queue.stage1_completed
and claim.node_finished(stage='1') both return true. There is no released
repair note, NQ delivery branch, or NQ return for this item.

The live generated server queue excludes the item, but the committed queue
and the launcher's shared clone still list it at stage 1. dispatch_all.py
uses the live queue to assign new work and claim.queue_stage to update held
claims, but a missing live row leaves the previously recorded stage intact.
Its _listed and _queue_stage checks read the committed shared clone.
Consequently NQ restarts completed work and correctly receives preflight's
"the item's node file is unchanged" rejection. Failure counts are not the cause.

This maintenance publishes only this item's removal from the four queue
records, with the two queue.md counts adjusted. The commit is based on
660bb7595e04ea5d6ec03f5a38eafa1039ee8860. All unrelated generated queue changes and staged work are
preserved with a private index. Each queue has adjacent live and HEAD
backups ending in .maint-NQ-proper-flat-polynomial-1792808566.bak. No mathematical or Lean file is changed.
The six existing test_stage1_repair_queue tests pass; no compiler is needed.

Protected-tool follow-up: reconcile held claims against the same live queue
used for scheduling, and publish completion-related queue removals with the
completion record so the shared clone agrees. This is a consistency repair;
it requires no failure-count exclusion, concurrency limit, or delay. The
launcher, review service and landing tools were not edited.

The next worker must preserve Q49's accepted split. Stage 1 is complete.
Do not submit the unchanged sandbox as a new split. Further stage-1 work
requires an explicitly released repair note; subsequent formalization must
follow the node's actual dependency readiness.
