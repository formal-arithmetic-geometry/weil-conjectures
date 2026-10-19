# Q26 maintenance: Quillen B comma homotopy fiber

Fixed the prerequisite dependency cycle and the upstream record inconsistency that made side-only repairs temporary. The item’s retained mathematics was not rewritten.

## Cause

The full `lem-coef-kan-quillen-right-proper` record bundles the model/right-proper foundation with coherent-localization pullback preservation. The latter depends on Brown localization, then discrete-fibration Quillen B, then this comma-fiber item. Existing `lem-coef-sharp-simplex-criterion` and `lem-coef-ex-infinity-finite-products` records cited that full theorem where their statements and proofs require only the already-existing independent `lem-coef-kan-quillen-model-right-proper-core`. Adding the candidate therefore closed the reported eight/six/nine-node cycle.

`coord/dag-sync.md` identifies `weil-conjectures-sheaf` as authoritative. The live copies still had the bad references. My initial side-only commits `93c224d5075fd298d31c9ff823fbfe81b1aa7e55` and `c7825916546fcfc3be4b3bed7f4614c0ea49f326` briefly passed, then sync `7e688d32c9` restored the faulty upstream records. The durable fix corrects both repositories. No dispatcher, provider, permission, compiler, review-service or landing-tool defect needed modification.

## Changes and commits

In BOTH server repositories, `/home/ubuntu/weil-conjectures-sheaf` and `/home/ubuntu/weil-newtargets`:

- `dag/nodes/sec-six-functors/lem-coef-sharp-simplex-criterion.json`
- `dag/nodes/sec-six-functors/lem-coef-ex-infinity-finite-products.json`

Replaced the broad theorem reference with the independent core in statement reference IDs, `stmt_deps`, proof uses/text references and `proof_deps`. Mathematical assertions, proof arguments, sources, Lean interfaces and historical metadata are retained.

Durable commits:

- Live `sheaf-dag`: `82ea37a3b6021159e5df4ae49ec3d30bf4637101`.
- Side `newtargets-dag`: `279aa08ceb8d88a0d21f036c36c632b7738ec56e`.

Both commits were made under `SHEAF_LEAD=L-only flock coord/.merge.lock`, using `Bin Wu <844524296@qq.com>`, with exact path selection. Backups precede edits: sibling `<filename>.maint-Q26-durable-20261017T055246Z.bak` on live and `<filename>.maint-Q26-durable-20261017T055258Z.bak` on side. Earlier side edits also have sibling timestamped backups.

The retained sandbox `report.md` has a maintenance handoff explaining the durable repair, preceded by `report.md.maint-Q26-durable-20261017T055403Z.bak`. The local launcher route note carries the same handoff. Protected launcher files, review/landing tools, scheduling and admission settings were not edited. No process was killed. No Lean file changed or Lean/Lake build ran.

## Validation

- Candidate overlay on both repositories: 158 reachable nodes, no missing dependency, no cycle. Restoring only the two old references in memory reproduces the exact nine-node cycle. Evidence: `closure-audit.txt`.
- Both repaired records pass side `tools/review_split.py`. The live checker also reports three historical children of Ex-infinity as already split; the same findings occur with the old references restored in memory and are unrelated to this repair.
- Full unmodified `tools/preflight_delivery.py Q26 lem-coef-quillen-b-comma-homotopy-fiber --base HEAD^` passed in isolated server worktree `/tmp/Q26-quillen-maint-preflight-1792215293`, candidate-only commit `da7b48d1df` on base `74f4297fa8`. Log: `full-preflight.log`. That candidate commit was made under the side merge lock with the required identity and was not pushed. The first scratch check rejected an untracked backup; the backup was preserved outside the worktree and the rerun exited 0.
- The active normal worker’s fresh `deliver.py --no-push` passed at `3907e13f0a` after the durable repair.
- Subsequent sync `c9d21ebed6` imported live tip `1a7de6fc761b43f623c873829fe580b9d0b1a524`, which includes `82ea37a3b6`; both repaired references remained correct after sync.

## Next worker

Retain the existing item JSON, searches, citations and independent-reading report. Refresh the normal base to a descendant containing the durable repair, then use the ordinary preflight/delivery path. The old cycle notes and the temporary pass at `2661647da9` are historical. Keep both prerequisites on the independent core; deleting this item’s equifibered-diagonal input would create a proof gap. Maintenance has repaired prerequisite records and validated the retained candidate, without replacing the normal item review/landing workflow.
