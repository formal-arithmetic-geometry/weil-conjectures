# NI maintenance: rational projective-line re-split

Item: `det-prop-p1-adjunction-rational-unit-counit`, stage 1, dispatcher key
`det-prop-p1-adjunction-rational-unit-counit@081ffe759`.

## Outcome

The cause is a delivery-contract conflict, confirmed against the worker logs,
retained packet, live repair record and current server checker. The necessary
repair is in protected delivery/landing tools. It has **not** been applied:
the maintenance instruction explicitly says not to edit launcher-owned files,
the review service or landing tools, and to describe the needed change here.
This report is not a successful repair or an item delivery.

No evidence from these failures calls for changing the mathematical statement
or discarding the worker's proof plan. I did not independently review the
mathematics of the retained split.

## Cause and evidence

1. `coord/repair-notes/det-prop-p1-adjunction-rational-unit-counit.json` on the
   Weil server is `state: released`, `stage: 1`, `keep_plan: true`. Its human
   decision dated 2026-10-27 expressly requests each extracted declaration's
   proof in words when available, permits statement-only `unsplit` nodes when
   it is not, requires preservation of every old argument in the children,
   and asks for separate `lean.declaration` / intended `lean.module` ownership.
   The dedicated entry in `coord/returns/NI.md` repeats that instruction.

2. `tools/preflight_delivery.py:454-467` on the server has no exception for
   this released instruction. It rejects any proof-bearing `unsplit` child
   and accepts new nodes only with status `unsplit` or `mathlib`. Consequently
   every proof-bearing `split` child is refused. Its repair-note-specific code
   around lines 359-398 only recognizes the older 2026-10-21 re-split rule;
   it does not implement this 2026-10-27 permission.

3. All five counted attempts (1793081184, 1793081850, 1793082145, 1793082357,
   1793082479) ended on the same three diagnostics, never on a mathematical
   error, compile error or provider refusal. The next already-running attempt
   1793082681 also reproduced them and ended BLOCKED:

   ```text
   new node lem-sfb-projective-normalized-unit-counit-restriction: status 'split'; a new node is unsplit or mathlib
   new node lem-sfb-rational-p1-localizing-preservation: status 'split'; a new node is unsplit or mathlib
   new node lem-sfb-rational-p1-unit-inversions: status 'split'; a new node is unsplit or mathlib
   ```

   The dispatcher continued dispatching after starting maintenance. I changed
   no failure count, dispatcher state, concurrency policy or claim.

4. There is a second, independent ownership handoff mismatch. The unmodified
   `batch2/deliver.py:127-138` filters new nodes through `SPLIT_OWNS` plus
   creation/source fields. `tools/node_fields.py` makes `lean` maintainer-owned;
   `tools/preflight_delivery.py:477-479` also refuses a new node carrying it.
   I executed the existing overlay function on the retained packet: both
   named declaration nodes enter with `lean`, leave without it, and retain
   only `lean_candidates`. Candidates preserve the request but do not perform
   ownership transfer. Relaxing only the status check would not fulfill the
   released repair order's ownership requirement.

5. The worker's missing-source disclosure is real: its read clone lacks
   `lean/Sheaf/Paper/RationalP1UnitCounit.lean`, while the server has it.
   Server lines 378-389 and 437-440 contain the requested named theorem holes
   `AlgebraicGeometry.ProEtale.RationalP1.localizingPreservation` and
   `AlgebraicGeometry.ProEtale.RationalP1.unitInversions`. There is also a
   `unitCounit_exact` hole at line 545; this report does not claim that the
   module has only two holes or that all its proof obligations are resolved.
   The server parent's `lean.declarations` still includes both requested
   declarations, and its `lean.note` records three original holes. The
   source-visibility mismatch did not cause the repeated status diagnostics,
   but must be resolved before reliable Lean signature/ownership verification.

The server HEAD observed during diagnosis was
`faaf2489ada844739f626efdf67bb5b47c369f70`. The latest committed change to
`tools/preflight_delivery.py` was `4b5957b44f354b14a2b4eb4ffa032fe0226ea61c`.
An unrelated existing uncommitted change makes unchanged-parent-statement
format findings advisory; it does not alter the child-status or ownership
checks. I did not stage or modify that change or other concurrent work.

## Validation performed

Read-only checks against the retained sandbox established:

- The parent statement is identical to the read clone's statement.
- `original-proof.json` equals the read clone's original twelve-step proof.
- The parent assembly has 3 steps / 1736 characters, below the requested 3000.
- The three children retain respectively 7 / 6 / 3 proof steps and
  6289 / 5009 / 2647 proof-text characters.
- The 12 original search records remain present. The unmodified delivery
  helper functions report PASS for citation quotations, logged searches and
  duplicate-report coverage.
- The unmodified overlay function reproduces removal of the two `lean`
  records while preserving their `lean_candidates` requests.

I used the recorded completed server dry runs plus current checker source to
confirm the status rejection. I did not launch another delivery or preflight,
modify the sandbox, compile Lean, run `lake build`, or stop any process.
No Lean source was changed, so no Lean compilation was needed.

Retained node SHA-256 fingerprints, for the next worker to recognize this packet:

```text
db01b9f7302fc505f2d4bda9308cba55cbb6cfcf4c052177ffc8b9e0de78f784  det-prop-p1-adjunction-rational-unit-counit.json
e81a07a26030d833abd63161b00e1eaa1cee2137edf830e09a420e9e435afaae  lem-sfb-projective-normalized-unit-counit-restriction.json
8c053c27111408d6bdd5991c801e6dd464e5acf36869b6edc27d676f8a61bfbb  lem-sfb-rational-p1-localizing-preservation.json
28b6f80a5aeb6fb076adac42dcae6c51757862cc5220b58df12678118f6ccea6  lem-sfb-rational-p1-unit-inversions.json
```

## Required changes for the tools' owner

Implement the released proof-bearing re-split permission consistently in the
normal delivery and independent review/landing path. A restricted exception
should derive authorization from the trusted released repair record, require
the unchanged parent statement and requested short assembly, and accept the
extracted proof-bearing children without weakening ordinary stage-1 rules.
Validate their proof steps, citations, dependency unions, search provenance
and DAG integrity; do not merely suppress the three diagnostics. Test both
this authorized packet and an ordinary unauthorized new `split` child.

Implement an explicit maintainer-verified ownership handoff for the two named
declarations. Resolve their exact server signatures against the child node
statements, keep the original public names, and record the real declaration
locations. An intended future module name is not evidence that the module
exists. `lean_candidates` can carry the request across stage 1; the normal
acceptance path must actually apply the verified transfer and reconcile the
parent's ownership. Do not globally let stage-1 workers overwrite arbitrary
maintainer-owned Lean metadata.

Make the existing server module available in the worker's advertised read
clone, or provide a supported source snapshot for this re-split. That requires
the owner of the protected shared-repository tooling to inspect the refresh
path; this session did not determine why that clone lacks the server file.

These are owner changes, not patches made or private bypasses created by this
maintenance session. Relabelling the children `unsplit` while carrying proofs
still fails. Removing their arguments would contradict the human's repair
order. Manually inserting them into main to avoid the new-node gate would
skip the normal independent review. None was done.

## Changes and handoff

Created this local `REPORT.md` and its `.bak`, and a durable copy with `.bak`
at `/home/ubuntu/weil-conjectures-sheaf/coord/maintenance/NI-rational-p1-resplit-contract-20261027.md`
on the server. The server report is committed under `coord/.merge.lock` with
`SHEAF_LEAD=L-only` and the requested Bin Wu identity; the resulting commit is
recorded below in the local report after the commit completes.

The next worker should retain
`/home/ubuntu/weil-newtargets-sandbox/NI/det-prop-p1-adjunction-rational-unit-counit`,
including all four node files, `original-proof.json`, `citations.json`,
`searches.jsonl` and the worker report. No searches or mathematics need to be
redone merely because these attempts ended BLOCKED. After the tools' owner
implements the contract and ownership repairs, refresh the base and use the
normal dry-run, delivery and independent review path. Until then the status
rejection remains reproducible; this maintenance record does not close it.
