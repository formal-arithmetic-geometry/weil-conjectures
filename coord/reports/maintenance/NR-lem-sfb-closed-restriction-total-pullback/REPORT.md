# Maintenance report: lem-sfb-closed-restriction-total-pullback

Date: 2026-10-24. Group NR, stage 2. Dispatcher key:
`lem-sfb-closed-restriction-total-pullback@19766f611` (26 failures at dispatch).
Maintenance workspace:
`/home/ubuntu/weil-launcher-all/maint/NR-lem-sfb-closed-restriction-total-pullback-1792833958`.

## Outcome and edit boundary

The cause is a server landing-reader bug, reproduced in this session. **The
implementation remains unfixed:** the user explicitly forbids editing landing
tools and says to describe their needed changes in REPORT.md instead. The
offending shared reader is `tools/stage2_delivery.py`, used by both preflight
and landing. No change to the local delivery wrapper or to the mathematics
would correct that reader. This report provides the required correction for
the landing-tool owner; it does not claim the item has been delivered or fixed.

## Cause

Server project: `/home/ubuntu/weil-conjectures-sheaf`.

In `tools/stage2_delivery.py`, function `read_delivery`:

1. Lines 953–957 find that the supplied existing node
   `lem-sfb-finite-closed-cover-resolution` is outside the item's prerequisite
   closure, emit a scope finding, and execute `continue`.
2. Consequently line 959 never places this supplied node in `D["deps"]`.
3. Lines 1141–1143 derive module owners from the item, new nodes, and
   `D["deps"]`. The cover node's real ownership is lost.
4. Lines 1231–1235 then reject its module
   `lean/Sheaf/AlgebraicGeometry/FiniteClosedCoverResolution.lean` as having
   no owning node. This failure is enforced by line 748.
5. Lines 1296–1299 classify the original scope finding as advisory, too late
   to undo its enforced ownership consequence.

This contradicts the reader's policy at lines 732–737: scope of repairs is
advisory and judged by the independent reviewer. The local
`/home/ubuntu/weil-launcher-all/batch2/deliver2.py` correctly stages all four
records and modules; the worker's final note misattributes the exclusion to it.
`tools/nt_preflight2.py:77`, `tools/preflight_delivery.py:185`, and
`tools/merge_delivery.py:810,938` all call the defective shared reader.

Current reader SHA-256:
`a1cfde63e885ab52ae48a6fe13d6daee107bd40f2f3623b9200ab226b2edc537`.
Latest commit touching it: `6f676dd9248e984c05227c739fa0102aa3a45c45`.
It is unchanged from the earlier maintenance diagnosis. Server HEAD when the
packet was compared: `1717b7058a009be5d7ef785555e63e2744d32a1a`.

## Authorization and packet evidence

The return in `coord/returns/NR.md`, dated 2026-10-24 07:05 UTC for immutable
head `19766f6117ab`, explicitly requires moving the helpers into definition
modules and making `FiniteClosedResolution` extend `FiniteClosedAugmentedRows`.
It also requires the cover node's lean-only record update with a note, or
reporting the merge tool's refusal. The cover node's live `proof_deps` already
contains this item. It is downstream; making it an item prerequisite merely
to pass the scope check would introduce a DAG cycle.

Against the live server records, the retained worker sandbox contains:

| Node | Changes | Module under lean/Sheaf/AlgebraicGeometry/ |
| --- | --- | --- |
| def-sfb-finite-closed-row-constructions | New definition node | FiniteClosedRowConstructions.lean |
| def-sfb-finite-closed-augmented-rows | New definition node | FiniteClosedAugmentedRows.lean |
| lem-sfb-closed-restriction-total-pullback | Only lean and stmt_deps | ClosedRestrictionTotalPullback.lean |
| lem-sfb-finite-closed-cover-resolution | Only lean | FiniteClosedCoverResolution.lean |

Sandbox:
`/home/ubuntu/weil-newtargets-stage2-sandbox/NR/lem-sfb-closed-restriction-total-pullback`.
The item's Lean file is byte-identical to
`baseline/ClosedRestrictionTotalPullback.lean.txt`. The cover module imports
the definition module and extends its structure, as the return requests.

## Verification in this session

* Inspected dispatcher state, current repair prompt, recent worker logs,
  `dispatch.log`, server return/delivery records, and available `~/cc1/*.log`.
  The landing logs yielded no matching refusal: this fails before publication.
* Worker run `1792833772/log.txt` stages all four records and modules and exits
  with exactly one enforced error: the cover module has no eligible owner.
  Its preceding prerequisite-scope message is explicitly advisory. The log is
  `/home/ubuntu/weil-launcher-all/run/NR/lem-sfb-closed-restriction-total-pullback.1792833772/log.txt`.
* Ran the complete, unmodified server `read_delivery` through the existing
  `tools/test_stage2_prerequisites.py:Prerequisites` fixture. Added a reverse
  proof edge from the supplied existing node to the item, then delivered only
  its Lean record and matching module along with the item. Assertions passed:
  exactly one scope advisory, supplied node absent from `D["deps"]`, and exactly
  one enforced ownerless-module failure. The temporary fixture was cleaned up.
  Its Git commits ran on the server under `SHEAF_LEAD=L-only flock
  coord/.merge.lock`, with the fixture's Bin Wu identity. No test/tool source
  was modified.
* Compared all four sandbox records to current server records and checked the
  item's source against its returned baseline. No Lean source was changed, so
  no new Lean compile was necessary. Earlier worker reports retain successful
  sequential compile evidence for the four modules. No `lake build` was run.
* No provider error was encountered. No processes were killed. No dispatcher
  state, counter, claim, concurrency setting, brief, delivery branch, review
  service, landing tool, DAG record, or Lean module was changed by this session.

## Required change by the landing-tool owner

In `read_delivery`, keep a well-formed supplied existing node available for
record checks, module ownership, effective graph validation, compile ordering,
and normal lean-only landing even when its scope objection is advisory. Keep
the scope advisory for independent review. The immediate defect is the
`continue` at line 957 after the scope finding; the intended local change is:

```diff
                 f("b", f"{p}: the node {nid} exists on the base and is not in the item's statement/proof prerequisite "
                        "closure on the base or as delivered: a delivery changes only the item, new definition nodes "
                        "and dependency nodes of the item")
-                continue
             bd = json.loads(git.show(base, p) or "{}")
             D["deps"][nid] = {"path": p, "node": nd, "base_node": bd}
```

This proposed change is documentation only; it has not been applied or
validated as a repaired landing implementation. Preserve genuine malformed
record, ownership, duplicate declaration, statement, compile, and graph checks.
Do not suppress ownerless failures globally, fabricate a prerequisite, assign
the cover module to a different node, or omit the required downstream repair.

Add a regression through the complete reader for a downstream node with a
reverse proof edge, a lean-only record change, and its matching supplied
module. Require the scope advisory to remain, the owner to be retained, and
the module to enter normal landing planning. Check that genuinely ownerless
modules, duplicate owners, and graph cycles remain enforced. Reconcile the
older prerequisite tests that still expect repair scope to be a hard failure
with the documented advisory policy.

## Changed paths, backups, and commit

Only maintenance documentation changes in this session:

* Local `REPORT.md`, with `REPORT.md.bak` preserved before the commit receipt.
* Server `coord/reports/maintenance/NR-lem-sfb-closed-restriction-total-pullback/REPORT.md`.
* The previous server report is preserved as
  `coord/reports/maintenance/NR-lem-sfb-closed-restriction-total-pullback/REPORT.md.maint-1792833958.bak`.

The server report and backup are committed together under `coord/.merge.lock`
with `SHEAF_LEAD=L-only`, author/committer Bin Wu
`<844524296@qq.com>`, and a path-limited commit so unrelated staged work is
excluded. The commit receipt is appended to the local copy after verification.

## Next worker

Preserve the existing F1/F2 packet and the item's statement; rebase stale
metadata normally. The actionable blocker is the shared landing reader above.
An identical packet against the unchanged reader will reproduce the refusal;
no additional mathematics addresses it. Failure counts remain diagnostic and
must not stop dispatching, throttle workers, or park this item.

Once the landing-tool owner has corrected and tested the reader, run:

```sh
python3 /home/ubuntu/weil-launcher-all/batch2/deliver2.py NR lem-sfb-closed-restriction-total-pullback --no-push
```

Require all four records and modules, including the downstream cover repair,
to reach effective delivery validation. Compile any changed Lean files one
at a time using `tools/lean_file.sh`, 60 seconds each; never `lake build`.
Then resume ordinary delivery and independent review.
