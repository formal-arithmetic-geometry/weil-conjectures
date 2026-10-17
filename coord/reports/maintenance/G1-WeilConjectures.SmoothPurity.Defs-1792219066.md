# WeilConjectures.SmoothPurity.Defs maintenance, 2026-10-17

Status: cause confirmed; the item remains blocked by a protected landing-tool policy. No
mathematical repair was delivered or claimed.

## Cause

The assigned source module has one hole, the body of
`AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityIso` in
`lean/WeilConjectures/SmoothPurity/Defs.lean`. It is an existing
`noncomputable def`, so any genuine repair must replace its body while keeping its
signature and attributes.

The server's `tools/stage3_gate.py:92-100` rejects every changed body in the adopted
`lean/WeilConjectures/` tree whose old declaration keyword is not `theorem` or
`lemma`. The rejection occurs before the repair lookup at line 106. It therefore
rejects a compiled, signature-preserving replacement of this existing sorried
definition. The current server `stage3_delivery.repair_job` authorizes only an
`XR...` reservation in `local/batch/repair` plus a matching claim; the G1 item has
no such reservation. The dispatcher has continued to count failures (41 at the start
of this maintenance run, 42 observed while it continued) because the same gate
refusal is deterministic.

This is a pipeline/tool policy mismatch. The source module compiles unchanged on the
server in 3.1 seconds with `tools/lean_file.sh`; the failure occurs before a
delivery can land. The retained sandbox candidate is also mathematically invalid:
`NormalizedWitness.lean` chooses arbitrary mutually inverse maps from a mere
existence theorem, without specifying the normalized purity construction. It must not
be delivered.

The broad relaxation in server commit `0f722051f9` was reverted by
`26cadb77f9` because it would admit arbitrary data-valued definition changes. The
needed repair is narrower: the tool owner must add an explicit authorization for this
existing assigned data hole (or an equivalent reviewed integration path), while
preserving the source-freeze checks for signatures, attributes, visibility, imports,
cycles, compile time, axioms, and sorry progress. An authorization must not be a
worker-controlled flag or a blanket exemption for definition bodies.

## Verification

- Read `run/G1/state-batch1.json`, all 45 prior worker-run directories, the retained
  sandbox report/change record, and the dispatcher/landing logs.
- Fresh server inspection shows the exact non-theorem-body test at
  `tools/stage3_gate.py:92-93), the repair lookup at lines 106 and
  `stage3_delivery.py:277-286`, and no G1 repair reservation.
- The live source module compiled with the required one-file command:
  `SHEAF_GROUP=maint-G1-smooth-purity-1792219066 SHEAF_FILE_TIMEOUT=60
  tools/lean_file.sh lean/WeilConjectures/SmoothPurity/Defs.lean` (exit 0,
  3.1 seconds). No `lake build` was run.
- Worker logs repeatedly report the same `stage3_gate.py` refusal. No provider
  429, gateway-concurrency, empty-answer, permission, or environment failure caused
  these attempts. No landing for this item appears in `coord/deliveries.log` or
  the checked `~/cc1/*.log` files.

## Required owner change

The owner of the protected landing tools should permit a narrowly authorized,
signature-preserving repair of an existing sorried source definition for this item,
or provide a reviewed integration route that leaves the upstream definition body
unchanged. The gate should still refuse changed concrete definitions, changed
signatures/attributes/public imports, new source declarations, hidden or newly added
sorries, and unauthorized repairs. Test the actual G1 path plus ordinary theorem
proofs and a data-valued definition regression. This maintenance run did not edit
`stage3_gate.py`, `stage3_delivery.py`, `preflight_delivery.py), the review
service, or any launcher-owned file because the maintenance instructions prohibit
editing landing tools and require the needed change to be described here.

## Changes and next worker

Changed paths:

- Working directory: `REPORT.md` and its empty pre-change backup
  `REPORT.md.bak`.
- Server: `coord/reports/maintenance/G1-WeilConjectures.SmoothPurity.Defs-1792219066.md`
  and its pre-change backup
  `coord/reports/maintenance/G1-WeilConjectures.SmoothPurity.Defs-1792219066.md.bak`.
  The report is committed under `SHEAF_LEAD=L-only flock coord/.merge.lock` with
  author `Bin Wu <844524296@qq.com>`.

No Lean module, node, brief, dispatcher state, claim, queue, admission setting,
concurrency cap, throttle, pause, review service, or landing tool was changed.

After the protected gate owner installs the narrow authorization, the next worker
should refresh the sandbox against current sources, discard the arbitrary-witness
candidate, construct the intended normalized purity data, run the full
`deliver3.py G1 WeilConjectures.SmoothPurity.Defs --no-push` path, and obtain an
independent second reading. Repeating the current delivery command before that gate
repair will reproduce the same refusal.
