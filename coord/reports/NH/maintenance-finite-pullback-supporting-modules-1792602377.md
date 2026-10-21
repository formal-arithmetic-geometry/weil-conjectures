# NH stage-2 maintenance: required supporting_modules rejected

Item: `lem-a1-finite-pullback-strict-tower-comparison`  
Dispatcher key: `lem-a1-finite-pullback-strict-tower-comparison@7de420383`  
Investigation date: 2026-10-21 UTC / 2026-10-22 Asia/Shanghai.

## Outcome

Cause identified and independently reproduced. The pipeline defect remains unresolved:
its repair is in the landing tools, which the maintenance request explicitly forbids
editing: “Launcher-owned files you must NOT edit (describe the needed change in
REPORT.md instead): ... the review service and the landing tools.”

This report supplies the diagnosis, exact repair location, validation requirements,
and worker handoff. No protected tool, dispatcher setting, node, or Lean source was
changed. No item delivery was pushed or merged. Dispatching was not limited or paused.
This is a deterministic format rejection, not a provider error or a mathematical failure.

## Cause and evidence

1. Server commit `461e0274ffc` added
   `lean.supporting_modules = ["Sheaf.Paper.AdicCoefficientDatumCompleted"]` to
   `dag/nodes/sec-proper-base-change/def-weil-pbc-adic-coefficient-datum.json`
   during a reviewed proof landing. The field survives on current main, including
   subsequent landing `e45110f31fc`.
2. The return at `coord/returns/NH.md:40` (head `7de42038356b`) expressly requires
   retaining that field in the dependency's section 1(B) record. It also requires
   definition-owner citations and the new existing-declaration tower-owner node.
   The return says the mathematics was checked and sound.
3. The retained sandbox implements those repairs, including the required metadata.
   Removing the field would undo the return rather than repair the pipeline.
4. Server `tools/stage2_delivery.py:45` still defines:

   ```python
   OPTIONAL = ("declarations", "file", "fixed_by", "note")
   ```

   `check_record` at lines 475–485 rejects all other keys. Its dependency-record
   call at line 1064 consequently rejects the required field. The tool's own
   header identifies it as the shared reader for stage-2 preflight, review, and
   merge: it is within the expressly protected landing-tool scope.
5. The actual path is:
   `batch2/deliver2.py` → SSH `tools/nt_preflight2.py` →
   `stage2_delivery.read_delivery` → `check_record`.
   The launcher wrapper reports the server refusal; its own format code is not
   where this particular failure originates. Fixing retries or permissions would
   not change this result.

Independent read-only reproduction on the server loaded the real sandbox record
over stdin and called the unmodified `stage2_delivery.check_record`. At observed
server HEAD `cca10bbad347153c00e2bd48adb09946f213d31a`, the tool blob was
`2f05021c90a438e5051b0fa5adcb2794a7cfbb34`. Results:

```text
packet_supporting_modules: ['Sheaf.Paper.AdicCoefficientDatumCompleted']
main_supporting_modules: ['Sheaf.Paper.AdicCoefficientDatumCompleted']
modules_exist: {'Sheaf.Paper.AdicCoefficientDatumCompleted': True}
accepted_optional_keys: ('declarations', 'file', 'fixed_by', 'note')
actual_record_findings:
  (b) dependency node def-weil-pbc-adic-coefficient-datum:
      lean has key(s) outside the format: supporting_modules
main_record_findings:
  (b) current main: lean has key(s) outside the format: supporting_modules
```

Thus even the published record fails this validator when passed with its own
recorded group. The supporting module exists at
`lean/Sheaf/Paper/AdicCoefficientDatumCompleted.lean`.

The latest completed worker log independently confirms the full delivery behavior:
`/home/ubuntu/weil-launcher-all/run/NH/lem-a1-finite-pullback-strict-tower-comparison.1792602400/log.txt:2411`.
Its dry run checked four Lean inputs on the server one at a time, staged the
packet, and ended at line 2431 with exactly one preflight reason: this unknown
key. Compilation failure and non-sorry warnings would have stopped the wrapper
before staging. Earlier repair logs show the same refusal repeatedly.

Dispatcher evidence:
`/home/ubuntu/weil-launcher-all/run/NH/state-batch2.json` records 12 tries for the
reported key at investigation start; `dispatch.log:262808` records this
maintenance launch. The failure count is an observation, not a stopping rule.
The inspected landing/build logs contained no matching landing of the repaired
packet; `coord/returns/NH.md` retains the outstanding return.

The same published metadata key appears on two other records:
`def-weil-pbc-bounded-constructible-complete` and
`lem-weil-pbc-integral-stratified-perfect-characterization`.
This is a shared schema mismatch, not an item-specific spelling error.

## Required change in protected tools

The owner authorized to change landing tools should repair
`/home/ubuntu/weil-conjectures-sheaf/tools/stage2_delivery.py`:

- Accept `supporting_modules` as an optional `lean` field in `OPTIONAL`.
- Validate its value as a list of nonempty module names; reject malformed values
  and keep rejecting unrelated unknown keys. Document the field in the stage-2
  record format. It must preserve supporting-module metadata on dependency
  interface replacements and must not substitute for declaration or import checks.
- Add a regression using the real-shaped NH dependency record. Check a valid
  supporting-module list, absent optional metadata, malformed metadata, and an
  unrelated extra key. Exercise the section 1(B) dependency path, since that is
  the path which fails here, and retain the existing public-import checks.
- Re-run the unchanged saved packet through the ordinary dry-run entry point;
  require zero preflight findings before delivery. All shared review/merge users
  must see the corrected schema, not just a special case in the wrapper.

No patched private copy, bypass, blanket acceptance of unknown keys, deletion of
required metadata, or mathematical rewrite was made. This report is the requested
handoff for the protected-code exception, not a claim that the repair has landed.

## Changes, backups, and commit

Only maintenance documentation is created by this session:

- Local `REPORT.md` in the maintenance working directory; `REPORT.md.bak` retains
  its pre-commit-reference version.
- Server `coord/reports/NH/maintenance-finite-pullback-supporting-modules-1792602377.md`,
  with an adjacent `.md.bak` copy. This is a new, separate maintenance report;
  the worker's delivery report is not overwritten. The server report is committed
  with the prescribed identity under `SHEAF_LEAD=L-only flock coord/.merge.lock`.
  The resulting commit is recorded below in the final local report.

No Lean file was changed or compiled during this maintenance investigation.
The successful sequential checks above are evidence from the completed worker's
ordinary dry run, not a new compile claimed by this session. No global build or
process termination was performed.

## Next worker

Continue with the existing sandbox:
`/home/ubuntu/weil-newtargets-stage2-sandbox/NH/lem-a1-finite-pullback-strict-tower-comparison`.
Keep the three Lean modules and four node records. The new node is
`def-a1-integral-finite-pullback-tower` with `existing: true` on
`Sheaf.Paper.IntegralOperationsWellDefined`. The item already cites
`def-a1-flat-term-kflat-complex`, `def-pur-integral-finite-pullback`,
`def-a1-principal-completed-koszul-towers`, and that new owner. It drops
`lem-pur-integral-operations-well-defined` from `stmt_deps` as requested. Both
existing dependency copies change only `lean`; the item's statement is unchanged.

Retain `lean.supporting_modules` on `def-weil-pbc-adic-coefficient-datum`.
Once the authorized schema fix is present, run:

```bash
python3 /home/ubuntu/weil-launcher-all/batch2/deliver2.py NH lem-a1-finite-pullback-strict-tower-comparison --no-push
```

After it passes, follow the ordinary delivery procedure. Any new Lean compilation
must remain one file at a time with the 60-second limit. Before the schema is
fixed, the same metadata rejection is expected; another mathematical rewrite
cannot repair it. No permission, provider, concurrency, or retry-limit change is
needed.
