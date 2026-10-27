# Q02 maintenance: supported Taylor presentation delivery

Item: `lem-trf-supported-taylor-presentation-pivots`, stage 2, returned head
`6f0f94694a09`, dispatcher key `lem-trf-supported-taylor-presentation-pivots@6f0f94694`.

**Cause confirmed; production repair requires a protected landing-tool change.**
The mathematics is not the blocker. The worker has already supplied the two new
definition nodes, five compiling modules, and both consumer-node Lean records.
No provider error was encountered in this maintenance run.

## Cause

The server's `tools/stage2_delivery.py:953` rejects
`lem-trf-formal-hilbert-stratum-minors` from the item's prerequisite closure.
That node is downstream: its `proof_deps` includes this item. Nevertheless,
return F2 in `coord/returns/Q02.md:52` explicitly requires extracting six
definitions from its module and changing that module to import the new
definition-owned module in the same delivery.

The scope finding is correctly classified as an ADVISORY by `enforced()` at
the end of `read_delivery()`, under the human's 2026-10-23 instruction implemented
by commit `f9e9a2640154a940db9aac47cce203a8bd7d6194`. But the `continue` at
line 957 has already omitted the node from `D["deps"]`. The module ownership
check at lines 1231–1235 consequently emits an enforced, misleading error:

```
lean/Sheaf/AlgebraicGeometry/FormalHilbertStratumMinors.lean:
no node of the delivery has it as lean.file
```

The sandbox does contain the owner node, and the local `deliver2.py` stages it.
The fault is in the shared server reader, used by both
`tools/nt_preflight2.py` and `tools/merge_delivery.py:810`, rather than in the
launcher delivery packaging. Changing only the dry-run wrapper would leave
landing broken. Adding the downstream theorem as an item dependency creates a
real DAG cycle and is not a valid repair.

The dispatcher correctly continued dispatching. Its seven-count maintenance
trigger is not a mathematical limit; the attempt logs show additional retries
of the same deterministic tool rejection. No retry/admission/concurrency setting
needs changing.

## Required protected change

In `/home/ubuntu/weil-conjectures-sheaf/tools/stage2_delivery.py`, remove only the
`continue` after the out-of-prerequisite-closure finding. Keep the finding, node
parsing, path checks, declaration/ownership checks, honesty checks and DAG checks:

```diff
@@ read_delivery: existing-node classification
                 f("b", f"{p}: the node {nid} exists on the base and is not in the item's statement/proof prerequisite "
                        "closure on the base or as delivered: a delivery changes only the item, new definition nodes "
                        "and dependency nodes of the item")
-                continue
             bd = json.loads(git.show(base, p) or "{}")
             D["deps"][nid] = {"path": p, "node": nd, "base_node": bd}
```

This restores the existing advisory policy: scope is reviewed, while a supplied
existing-node record remains available to validate and own its module. It does
not disable the enforced ownership error for genuinely ownerless modules.

The user explicitly prohibited editing “the review service and the landing
tools” and directed that needed changes be described in REPORT.md instead.
`stage2_delivery.py` is a landing tool shared by `merge_delivery.py`, so its
production source was not edited. The proposed change was executed only in a
temporary Python module in memory. **The production blocker is still present.**

## Changes and commits

New files in this maintenance working directory:

- `REPORT.md`: this report.
- `verify_scope_snapshot.py`: read-only replay harness for the actual packet;
  it loads the proposed change in memory and creates no Git commits or refs.
- `evidence/current-dry-run.log`: fresh reproduction through the prescribed
  `deliver2.py --no-push`; all five files compiled separately on the server,
  then the single ownership error reproduced.
- `evidence/scope-replay.log`: original versus proposed reader results.
- `evidence/packet.json`: snapshot of the five sandbox node files, five Lean
  modules and worker report used by the replay.
- `evidence/stage2_delivery.py`, `evidence/nt_preflight2.py`,
  `evidence/nt_srv_compile.py`: read-only server source snapshots.

Server documentation and replay harness to commit under `coord/.merge.lock`:

- `coord/changes/Q02-supported-taylor-delivery-scope.md`
- `coord/changes/Q02-supported-taylor-delivery-scope-replay.py`

The server documentation commit is identified in the appended local commit
receipt and by `git log -- coord/changes/Q02-supported-taylor-delivery-scope.md`.

No existing sandbox file, Lean module, DAG record, dispatcher state, launcher
code, review service or landing tool was changed. Existing files are backed up
with `.bak` before any edit; newly created documentation has no prior version.
No delivery was pushed. No lake build was run and no foreign process was killed.

## Verification

The read-only server replay used immutable base
`fe4adca51a707e27443f9dd0465cbdcb45570b94` and server reader SHA-256
`a1cfde63e885ab52ae48a6fe13d6daee107bd40f2f3623b9200ab226b2edc537`.

- Original reader: exactly the reported ownership failure; downstream owner
  absent from `D["deps"]`.
- Candidate reader: both consumer nodes retained, all five modules recognized,
  scope finding still advisory, no enforced failures, incremental DAG clean.
- Negative controls: removing the actual owner still fails; a wrong recorded
  signature still fails; an added axiom still fails; adding the downstream
  theorem as a dependency still reports a cycle.

Reproduce on the server using the committed harness and a JSON path-to-source
mapping of the retained sandbox packet. The local `evidence/packet.json` is the
snapshot used here. The harness performs no Lean compilation; the fresh dry-run
log records the separate server compilation result. No Lean source was edited
in this maintenance run.

## Next worker

Keep the completed F1/F2 sandbox repair at
`/home/ubuntu/weil-newtargets-stage2-sandbox/Q02/lem-trf-supported-taylor-presentation-pivots`.
Do not redo the mathematics or add a dependency on the downstream theorem.
The owner must deploy the protected reader correction above before a retry can
deliver. Then compare both consumer modules and node records with current main,
run `python3 /home/ubuntu/weil-launcher-all/batch2/deliver2.py Q02
lem-trf-supported-taylor-presentation-pivots --no-push`, and deliver normally
after it passes. Preserve the F1/F2 new definitions and consumer import repairs.
There is no need to reset the failure count or stop dispatching.
