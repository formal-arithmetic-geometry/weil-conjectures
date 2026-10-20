# N9 maintenance: cor-sf-duality-pullback

2026-10-20. Stage 2, dispatcher key `cor-sf-duality-pullback@new`.
Project: `/home/ubuntu/weil-conjectures-sheaf` on `the project server`.

## Outcome

The current repeated failure is an upstream-sync quarantine combined with a
stale worker brief, not a missing mathematical definition or an SSH permission
failure. The dependency repair already exists in X2's delivery; it was not yet
landed or published at the check below. This maintenance does **not** claim the
item is fixed or that its saved statement compiles.

Historical provider HTTP 429 failures were also found in this item's logs.
Under the user's instruction, “a provider error ... is not yours to fix: say so
in REPORT.md and stop,” repair work stopped upon finding them. No provider,
retry, admission, dispatch, review, or landing implementation was changed.

## Current cause and evidence

1. The saved report, recent worker prompts/logs, dispatcher state, and
   `dispatch.log` agree: the retained packet's dry run and an isolated import of
   `Sheaf.Paper.SixFunctorDatum` fail before statement elaboration because
   `Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses.olean` is absent.
   The separate Mathlib control passes. Repeating the same statement compilation
   cannot repair that library state.
2. Server commit `29b1c235f457bada4f1add891a0e6ae4fa47bf69`, at
   2026-10-20 10:47:54 UTC, records upstream sync `5f7b33eac` moving 137 failing
   modules and 2312 importers into `quarantine/`. `coord/rework.tsv` records the
   root failure: importing the Sheaf and WeilConjectures hypercohomology modules
   declares `CategoryTheory.ringedSiteZerothHypercohomology` twice.
3. `git ls-files` and direct source inspection locate the root and datum in
   `quarantine/Sheaf/`, rather than `lean/Sheaf/`. The shared read clone also
   contains the quarantined copies of `SixFunctorDatum`,
   `SixFunctorDualNotation`, `IntrinsicCoefficientTwistsUnrestricted`, and
   `VerdierExchange`. The saved worker report's statement that the dependency
   sources cannot be obtained therefore omits the quarantine tree.
4. `batch2/scompile.py --source` searches live source paths using
   `tools/stage2_delivery.py:existing_file`; neither includes quarantine.
   “Module source unavailable” is consistent with that implementation. It does
   not establish that the source was lost. Quarantined code must not silently
   become an approved compilation dependency.
5. The new/retained stage-2 prompt checks dependency Lean records, which remain
   present despite quarantine. It appends the previous BLOCKED note and directs
   another dry run, but supplies no current quarantine or root-repair context.
   In `dispatch_all.py`, route notes are appended near lines 641–643; pending
   requests replay stored `extra` near lines 754–763; rework-specific instructions
   are appended only in the stage-3 branch near lines 819–822. There is no route
   note for this item. Thus the repeated attempts reproduce an environmental
   failure while being briefed to treat it as an item-local problem.

## Existing repair and publication status

X2 delivery branch:
`deliver/X2/Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses`

Delivery commit: `68becc60fe7e7d4edf36fe4d653a7e24a46014ef`.

The inspected patch restores the existing proved root from quarantine and
changes `lean/Sheaf/Algebra/Homology/RingedSiteZerothHypercohomology.lean` to
publicly import the canonical upstream definition instead of declaring it again.
Its report records successful single-file compilation of the compatibility
module, root, and two direct consumers. Those are X2's reported validations;
this maintenance did not independently compile or approve the delivery.

At approximately 13:16 UTC, the live root was still absent and
`tools/review_class.py X2 Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses`
returned `AUTO`. The landing log had no current X2 landing for that root; its
older E3 landing is from 2026-10-19 and predates quarantine. The latest inspected
`local/builds/published.json` reported green commit
`89421ca049a44e986f8a47898d484955b2974351`, published at 13:11:28 UTC.
That green build excludes the quarantined root and does not establish that this
item's dependencies are available.

The earlier merge-lock deadlock described in
`coord/reports/maintenance/N8-prop-sf-pf-coherence-1792501236.md` was already
repaired by other maintenance. Ordinary landings resumed at 13:11–13:12 UTC.
It is not evidence that X2's root or its quarantined importer chain has landed.

## Provider evidence and stop

`run/N9/cor-sf-duality-pullback.1792436019/log.txt` contains:

- Lines 10266–10270: exhausted retry, HTTP 429 Too Many Requests,
  request `92a3381b-2e28-414e-a873-907ddb416715`, followed by recovery 1.
- Lines 10760–10764: HTTP 429, request
  `dc08d72b-a92b-46c2-89fc-b7f02291ed5d`, followed by recovery 2.
- Lines 10861–10865: HTTP 429, request
  `a17954fd-aa4a-4f67-adf1-22ba556c7095`, followed by recovery 3.

These historical provider interruptions are separate from the later reproducible
missing-object failures. No attempt was made to repair the provider or introduce
any concurrency restriction, throttle, admission limit, dispatch pause, or
failure-count cutoff. The user's provider-error stop rule was followed.

## Changes, backups, commits

The only new artifact is this report and its server archival copy at
`coord/reports/maintenance/N9-cor-sf-duality-pullback-1792502055.md`.
Report snapshots use the `.bak` suffix. No pre-existing project, launcher, node,
or sandbox file was edited. In particular, the retained Lean module and report
were left intact while their worker may still be running.

The archival copy is committed on the server under `coord/.merge.lock` with
`SHEAF_LEAD=L-only` and the required Bin Wu identity. The resulting commit is
recorded in the accompanying `server-commit.txt` and in the path's git history.
No Lean compilation, Lake/global build, process termination, delivery push, or
quarantine restoration was performed by this maintenance.

## Required protected-owner follow-up

`dispatch_all.py`, the review service, and the landing tools are explicitly
protected by the user's maintenance instructions. They were inspected, not
edited. The remaining change must be made by their owner:

- Refresh quarantine/rework context when constructing **all** stage-2 prompts,
  including retained and pending requests. Resolve the dependency modules against
  current `coord/rework.tsv`, not just the existence of their DAG Lean records.
  Include the source's quarantine path, exact root diagnostic, existing repair
  branch/head, and current landing/verification status. Preserve dispatch and
  failure accounting; do not add a scheduling restriction or pause.
- Preserve the source reader's distinction between live and quarantined code.
  A diagnostic may identify the quarantine path and root repair rather than
  misleadingly implying that the source is lost; it must not silently feed
  quarantined modules to compilation as a usable library.
- Process X2's existing root repair through normal landing/verification, then
  restore its affected importer chain through the existing rework workflow.
  The missing compiled object is not corrected by resetting this item's tries,
  deleting its sandbox, or adding a copy of the datum to its mathematical packet.

## Next worker

Retain
`/home/ubuntu/weil-newtargets-stage2-sandbox/N9/cor-sf-duality-pullback`.
The saved statement has **not** been certified. Its report explicitly says the
earlier clean compile referred to an older implementation; the current version
contains four coefficient stages and explicit identity/composition/smooth laws.

Read the current node and canonical dependency declarations, and inspect
`coord/rework.tsv` and the read-only `quarantine/` sources to understand an
absent module. Check the current status of the X2 root repair and the complete
import chain rather than assuming its delivery is a published build. Continue
using the prescribed single-file compiler and dry-run/delivery tools under the
stage-2 brief. Once dependencies load, repair actual elaboration diagnostics,
perform the clause-by-clause self-check, synchronize the Lean record, and deliver.
This maintenance supplies no mathematical weakening or alternate definitions.
