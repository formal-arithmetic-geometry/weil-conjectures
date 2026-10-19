# Q51 maintenance: def-sfb-dc-lower-star

The original return of f1cd301618 was missing maintainer-owned chapter/unit
metadata, not a mathematical defect. The returned reader passed the definition
and its citations. The retained sandbox already had the requested bindings, but
deliver.py correctly keeps these fields from the authoritative delivery base;
repeating a sandbox-only edit could never repair that base.

During this maintenance investigation the pipeline's snapshot-wide metadata
repair landed: live be148130e20df307acc3a28209581384702f1fd4, side
30002d787829c936450ebabf0918ee2d1720634c. Those commits (not authored by this
maintenance session) installed dag/chapters/sec-six-functors-basics.json,
dag/units/sk-def-sfb-dc-restricted-functors.json, and this item's bindings:
chapter sec-six-functors-basics, unit sk-def-sfb-dc-restricted-functors.
Both committed server trees have been checked. A selected units.py generation
preview proposes no further change. Live-to-side sync reads committed live DAG
metadata, so both ends now agree.

The most recent retries instead stopped healthy queued delivery processes after
60 seconds. Stage 1 and stage 2 deliveries for Q51 share deliver-Q51.lock;
the lock holder observed during maintenance advanced into preflight and exited.
The following holder was the group's stage-2 dry run. No stale lock or permanent
deadlock was established. Waiting for the group, pool or fetch lock can exceed
60 seconds. The Lean single-file compile limit does not limit stage-1 delivery.

This maintenance installs a focused route note in the deployed launcher's
route-notes/def-sfb-dc-lower-star.md and versions it at
tools/launcher/route-notes/def-sfb-dc-lower-star.md. dispatch_all.py reads that
note for new writing/repair attempts without restarting the dispatcher.
Second readers receive the recovery in the retained report.md. It tells workers
to retain the reviewed mathematics, use the repaired base and wait for an
actual delivery result. The historical return below is now marked recovered.

Ordinary unchanged deliver.py --no-push validation passed; see below. Maintenance pushes no
item delivery, resets no failure counters, and kills no other worker process.
No Lean file or mathematics was changed and no compiler or Lake build ran.
Every edited file has an adjacent .maint-Q51-lower-star-1792159340.bak backup
(empty for a newly created file). Only the maintenance handoff files are staged.


## Successful ordinary validation

The active dispatcher worker ran the required unchanged command:

    python3 /home/ubuntu/weil-launcher-nt/deliver.py Q51 def-sfb-dc-lower-star --no-push
    OK (not pushed) deliver/Q51/def-sfb-dc-lower-star at 83fc6199c8: preflight passed

The log reports a successful exit after 544113 ms (about nine minutes including
the queues). Full candidate 83fc6199c8c61f27de27eb758c59d34fcd11b0de.
Before preflight ended, maintenance checked that candidate's correct bindings,
chapter record and unit record. The mathematical fields statement, stmt_deps,
proof, proof_deps and proof_origin match the reviewed f1cd301618 packet exactly.
The result is archived in Q51-dc-lower-star-validation.json beside this note.

Once that result was available, maintenance interrupted only its own still
queued duplicate PID 2408243. Its intentional exit 130 is not a failed
preflight; the ordinary worker's completed result is the validation above.
The retained report.md now carries recovery and validation entries so the next
second reader sees them despite route notes being limited to writing briefs.
Continue the normal second-reader delivery. No item delivery was pushed by
maintenance; no failure counter, claim or dispatcher process was changed.
