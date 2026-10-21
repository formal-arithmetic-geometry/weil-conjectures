# NH stage-2 maintenance: supporting-module schema mismatch

Item: `lem-a1-finite-pullback-strict-tower-comparison`  
Dispatcher key: `lem-a1-finite-pullback-strict-tower-comparison@7de420383`  
Investigation: 2026-10-22 Asia/Shanghai (2026-10-21 UTC).

## Result and restriction

The cause is a deterministic server validator defect, independently reproduced
against both the saved packet and the published dependency record. It remains
unfixed because the necessary change is in a protected landing tool. The user's
instruction explicitly says: "Launcher-owned files you must NOT edit (describe
the needed change in REPORT.md instead): ... the review service and the landing
tools." This report follows that exception; it does not claim a working repair.

`tools/stage2_delivery.py` identifies itself as the shared reader for preflight,
review, and merge. Editing it, patching a private copy, or removing required
metadata to pass its check would violate the request or the outstanding return.
No approval is requested. No item mathematics, worker packet, launcher tool,
landing tool, dispatcher state, or concurrency setting was changed. Dispatching
was not paused or limited. This is not a provider-error diagnosis.

## Cause and evidence

1. Reviewed server commit `461e0274ffc405dd25a5e3edd03e25a3da23f83d`
   introduced `lean.supporting_modules` on
   `dag/nodes/sec-proper-base-change/def-weil-pbc-adic-coefficient-datum.json`:
   `["Sheaf.Paper.AdicCoefficientDatumCompleted"]`. The field remains on live
   main, and the named supporting module exists. Two other live DAG records also
   carry this key: `def-weil-pbc-bounded-constructible-complete` and
   `lem-weil-pbc-integral-stratified-perfect-characterization`.
2. `coord/returns/NH.md:40`, for returned head `7de42038356b`, explicitly requires
   retaining that field on the dependency's section 1(B) record. Its mathematics
   review says the item is sound. The packet includes the requested field and
   the requested definition-owner repairs.
3. Server `tools/stage2_delivery.py:45` still has:

   ```python
   OPTIONAL = ("declarations", "file", "fixed_by", "note")
   ```

   `check_record` at lines 475-485 rejects keys outside `KEYS + OPTIONAL`.
   `read_delivery` applies that check to dependency records at line 1064.
   Execution reaches it through
   `batch2/deliver2.py -> tools/nt_preflight2.py -> stage2_delivery.read_delivery`.
   The wrapper is reporting the server failure; permissions, retries and the
   item's mathematics cannot repair this missing schema entry.
4. A fresh read-only reproduction imported the actual server module and passed
   the actual sandbox record into its unmodified `check_record`. It separately
   checked the published record with that record's own `by` value. At observed
   HEAD `125ddf0eb78c06dada4a9ec539093435be4a6497`, tool blob
   `2f05021c90a438e5051b0fa5adcb2794a7cfbb34`, the results were:

   ```text
   optional: ('declarations', 'file', 'fixed_by', 'note')
   packet_supporting_modules: ['Sheaf.Paper.AdicCoefficientDatumCompleted']
   live_supporting_modules: ['Sheaf.Paper.AdicCoefficientDatumCompleted']
   supporting_module_exists: True
   packet_findings: [('b', 'dependency node def-weil-pbc-adic-coefficient-datum: lean has key(s) outside the format: supporting_modules')]
   live_findings: [('b', 'live dependency record: lean has key(s) outside the format: supporting_modules')]
   ```

5. The completed worker's ordinary dry run is independently visible in
   `/home/ubuntu/weil-launcher-all/run/NH/lem-a1-finite-pullback-strict-tower-comparison.1792604240/log.txt:1644`.
   It reports checking four Lean inputs one at a time, stages the three modules,
   four node records and report, then reports exactly one preflight failure at
   lines 1660-1661: the unsupported key. No packet was pushed. This maintenance
   did not repeat Lean compilation: the unchanged schema was reproduced
   directly, and no Lean file was changed.
6. Dispatcher state recorded 20 tries for this key at investigation start;
   `dispatch.log:263520` records this maintenance launch. An earlier maintenance
   report already documented this exact defect in server documentation commit
   `26b222359269a64e9b21d18a9f7ee9f962ae149a`. The validator blob is unchanged
   since that investigation. Documenting a protected-tool repair did not deploy
   it, so continued retries reach the same rejection. Failure counts are not a
   reason to stop dispatching.

## Required protected-tool change

The owner authorized to edit landing tools must update
`/home/ubuntu/weil-conjectures-sheaf/tools/stage2_delivery.py` so the shared
stage-2 schema accepts the already-published optional `lean.supporting_modules`
field. Validate it as a list of nonempty module names; keep rejecting malformed
values and unrelated unknown keys. Document this metadata in the record format
in `coord/brief-stage2.md` section 5. Preserve it through dependency-interface
replacements without weakening declaration, public-import, ownership, or compile
checks. Changing only the launcher wrapper would leave review/merge inconsistent.

Regression coverage should include a real-shaped NH section 1(B) dependency
record with the valid list, absence of the optional field, malformed list/string
values, and an unrelated extra key. The ordinary preflight must accept the valid
record and still reject malformed records. Then run the unchanged saved packet
through the ordinary `deliver2.py --no-push` path and require a clean result.
Do not delete the metadata, bypass validation, rewrite the mathematics, or add
any dispatch limit to conceal this failure.

## Changes, backups, and server commit

Only maintenance documentation is created:

- Local `REPORT.md` in this working directory. `REPORT.md.bak` preserves the
  version before adding the final server commit reference.
- Server `coord/reports/NH/maintenance-finite-pullback-supporting-modules-1792604435.md`,
  with an adjacent `.md.bak` snapshot. This separate report leaves the worker's
  report and the earlier maintenance report intact.

The server report is committed alone under `SHEAF_LEAD=L-only flock
coord/.merge.lock`, using `Bin Wu <844524296@qq.com>`. The local report will
record the resulting commit after verification. No Lean source was changed or
compiled, no global build ran, and no process was killed.

## Next worker

Continue from
`/home/ubuntu/weil-newtargets-stage2-sandbox/NH/lem-a1-finite-pullback-strict-tower-comparison`.
Preserve the three Lean modules and four node records. The item already drops
`lem-pur-integral-operations-well-defined` from `stmt_deps` and cites
`def-a1-flat-term-kflat-complex`, `def-pur-integral-finite-pullback`,
`def-a1-principal-completed-koszul-towers`, and the new
`def-a1-integral-finite-pullback-tower`. That new owner has `existing: true` on
`Sheaf.Paper.IntegralOperationsWellDefined` and records the tower, levels,
restriction, and canonical transition definitions. Retain the required
supporting-module metadata on `def-weil-pbc-adic-coefficient-datum`.

After the protected schema repair is actually deployed, run:

```bash
python3 /home/ubuntu/weil-launcher-all/batch2/deliver2.py NH lem-a1-finite-pullback-strict-tower-comparison --no-push
```

Then follow the normal delivery/review procedure. Compilation must remain one
file at a time with the 60-second limit and no `lake build`. Until the schema
changes, another retry is expected to hit the same error; a documentation commit
is not evidence that the validator was repaired.
