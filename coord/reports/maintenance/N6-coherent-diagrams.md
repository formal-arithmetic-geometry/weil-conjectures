# N6 maintenance: coherent diagram model dependency cycle

Item: `lem-coef-simplicial-model-coherent-diagrams`, stage 1, dispatcher key `lem-coef-simplicial-model-coherent-diagrams@98f837736`. Maintenance date: 2026-10-17.

The repeated failures were caused by circular supporting-node dependencies outside the worker's permitted edit scope. This was a DAG data problem, not a failure-count limit or a Lean compiler failure. The circular foundations have been repaired in both the authoritative live project and the newtargets snapshot.

## Cause and evidence

The original delivery `98f8377362` was returned for a changed rectification citation. Workers repaired citations, but fresh preflight exposed successively larger dependency cycles (15, 21, 29, then 33 nodes as the live DAG evolved). Dispatcher log entries at 04:52, 05:26, 06:37 and 06:59 on October 17 record that repairing the cycles required forbidden supporting-node edits. Re-dispatching the same scoped brief could not repair that data.

The item's localization, Smith/accessibility and enriched-rectification dependencies reached two supporting nodes which depended back on the item:

- `lem-coef-infinity-functor-pushout`, Steps 2 and 7, used the item for existence/universe facts about Cat-infinity and for a path-object cospan computation.
- `lem-coef-space-geometric-descent`, Steps 2 and 3, used the enriched diagram-model item for ordinary diagrams of spaces.

There was also a persistence issue: `/home/ubuntu/weil-newtargets` is a synchronized side snapshot. `tools/sync_newtargets.py` imports authoritative records from `/home/ubuntu/weil-conjectures-sheaf`. An initial side-only repair was overwritten by sync commit `19f4422e6b` (`Sync live DAG 971db6c0a4fa`). The durable repair therefore had to be committed in the authoritative live repository first, then aligned in newtargets. No synchronization or validation gate was disabled.

## Changes and commits

All paths below are relative to the server repositories. All server commits used `SHEAF_LEAD=L-only` while holding that repository's `coord/.merge.lock`, with author Bin Wu <844524296@qq.com>. Existing files were backed up before changes; `.bak` files remain beside the affected files. New handoff/evidence files also have final backup snapshots.

Authoritative repository `/home/ubuntu/weil-conjectures-sheaf`:

- `700b3436c6` — repair the two supporting proofs and add their independent foundation.
- `1fc5daf01a` — preserve the original `\natural` TeX commands after a text-conversion error in the repair script.
- `78933aa91c` — retain complete, verbatim Mathlib search outputs for the new foundation.

Matching repository `/home/ubuntu/weil-newtargets`:

- `c227dedff4` — align the durable three-node repair with the authoritative DAG.
- `6d51610d58` — matching TeX correction.
- `211ae91c72` — matching verbatim search evidence. Maintenance-handoff installation is recorded in `evidence/handoff-installation.txt`.

Changed mathematical records, all in `dag/nodes/sec-six-functors/`:

- New `lem-coef-cat-infinity-colimits-cartesian-closure.json`: an independent statement-only foundation for small limits/colimits, cartesian closure, coherent internal Homs and universe enlargement. It cites precise HTT locations and depends only on the existing enhanced-diagram conventions. It remains `unsplit`, with empty proof and proof dependencies. Four genuine Mathlib searches and their raw results are retained; no matching infinity-categorical theorem was found.
- `lem-coef-infinity-functor-pushout.json`: use that foundation in Step 2; replace the circular cospan invocation in Step 7 by the direct mapping-Kan-space path-object calculation, retaining the actual coherent cone and transformations. The original exponential/pushout argument is retained.
- `lem-coef-space-geometric-descent.json`: use existing independent ordinary-index rectification and model-colimit comparison; justify free-map cofibrancy by the free/evaluation lifting adjunction. Its theorem statement is unchanged.

Earlier side commits `6e6cf276f9` and `6536ef80f6` were the initial repair attempts; the authoritative repair supersedes them. Side commit `6fa3729bca` installed the already-written statement-only `lem-coef-enriched-diagram-size-generation.json` unchanged from the worker sandbox, including its search records. Delivery now correctly excludes its unchanged copy.

Handoff files:

- Server `coord/reports/maintenance/N6-coherent-diagrams.md` and adjacent `N6-coherent-diagrams-evidence/` archive.
- Server `tools/launcher/route-notes/lem-coef-simplicial-model-coherent-diagrams.md`.
- Local `/home/ubuntu/weil-launcher-nt/route-notes/lem-coef-simplicial-model-coherent-diagrams.md`.
- Appended maintenance section in the item's sandbox `report.md`; the worker's proof and statement were not edited by maintenance.

## Validation and limits

`evidence/server-validation.txt` records that both repaired supporting proofs pass `review_split.py`, all three repaired/new records match their committed versions in both repositories, and a read-only traversal of the original full dependency set finds 354 reachable nodes, zero cycles and zero missing nodes. The audit reinstates the original Smith/accessibility/rectification/localization dependencies in memory; it does not rely on the concurrent worker deleting citations.

The active worker's server DAG check passed. Its full `deliver.py N6 lem-coef-simplicial-model-coherent-diagrams --no-push .` dry run passed at `d1924d6a86` (`preflight passed`). A subsequent report-only rerun was still running when the handoff was prepared. The relevant log excerpt is preserved in `evidence/worker-preflight.txt`.

The whole-project cycle checker still reports unrelated existing SCCs. These do not involve the item or the repaired nodes. This report does not claim global DAG cleanliness or a mathematical review of the current item proof. The new unsplit foundation intentionally does not pass a split-proof review. No Lean file changed, so no Lean compilation was required or run; no `lake build` was run. No process was killed. Failure counters and dispatcher state were left to the running dispatcher.

## Next worker / second reader

The full original dependency set is now acyclic. Keep or restore existing Smith recognition, accessibility, enriched rectification and simplicial-model nerve-localization citations where the argument needs them, regenerating current verbatim citation entries.

The concurrent repair worker independently removed those citations and expanded Steps 3, 5, 7, 9 and 10 into direct arguments. The reader must check those arguments for complete justification; a passing DAG check is insufficient. The worker report's explanation that citations had to be removed to fix the cycle is superseded by this maintenance result. Maintenance deliberately did not undertake the item's mathematics.

Continue normal stage-1 review/delivery. Do not count the already-existing size-generation node as newly delivered, and do not claim the new Cat-infinity foundation has a split proof or Lean attachment. If a supporting back edge returns after synchronization, repair the authoritative live record under its merge lock before aligning the snapshot; changing only the side record is not durable.
