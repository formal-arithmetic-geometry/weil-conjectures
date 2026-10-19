# Maintenance: Quillen B comma homotopy fiber (Q26)

The repeated stage-1 preflight failure was a real dependency-cycle defect in prerequisite records. The existing Kan–Quillen node bundled its elementary model/right-proper foundation with a coherent-localization pullback conclusion. The latter uses Brown fibrant localization, whose proof uses discrete-fibration Quillen B, which uses the assigned comma-fiber item. The candidate comma-fiber proof uses the bisimplicial diagonal tools; these tools and their sharp/pullback foundations cited the entire bundled Kan node even where they needed only the model/right-proper clauses. Splitting the comma theorem could therefore close the cycle; retrying the same base could not fix it.

The repair preserves the complete statement of `lem-coef-kan-quillen-right-proper` and all existing mathematical assertions. It extracts `lem-coef-kan-quillen-model-right-proper-core`, comprising exactly the original model structure, functorial factorization, boundary/horn-cell descriptions and right properness clauses, with the original complete proof steps 1–6 copied verbatim. Its 61-node prerequisite closure contains neither Quillen B nor the full Kan parent. Hovey, Model Categories, Propositions 3.2.2–3.2.3 and Theorems 3.6.4–3.6.5 are the recorded sources; the inherited LeanSearch/Loogle/LeanFinder/grep searches already address these exact model/right-proper claims.

The full Kan parent obtains those clauses from the core and retains its Brown/cone-calculus proof of coherent-localization pullback independence. Thirteen existing users cite the core for model/right-proper facts. Uses of strict pullbacks as path homotopy pullbacks instead cite the existing path comparison and invariance theorems. For the arrow-morphism calculation, explicit sections of the trivial fibrations give a strictly commuting map of Kan cospans, as required by the invariance theorem. The equifibered sharpness argument uses arbitrary non-Kan sources via right properness and the stated sharpness characterization. Historical review/provenance metadata is preserved. No Lean module, launcher tool, review tool, landing tool, scheduling/admission setting or item mathematics was changed.

Changed records, in `dag/nodes/sec-six-functors/`, on both server repositories:

- `lem-coef-kan-quillen-model-right-proper-core.json` (new independently proved stage-1 record)
- `lem-coef-kan-quillen-right-proper.json`
- `lem-coef-bisimplicial-diagonal-equivalence.json`
- `lem-coef-equifibered-bisimplicial-diagonal.json`
- `lem-coef-infinity-arrow-morphism-square.json`
- `lem-coef-infinity-homotopy-pullback-pasting.json`
- `lem-coef-infinity-join-cone-calculus.json`
- `lem-coef-kan-pullback-fibration-invariance.json`
- `lem-coef-kan-pullback-path-comparison.json`
- `lem-coef-rezk-diagonal-sharp.json`
- `lem-coef-sharp-pullback-calculus.json`
- `lem-coef-sharp-simplex-criterion.json`
- `lem-coef-sharp-special-colimit-gluing.json`
- `lem-coef-sset-anodyne-pushout-product.json`
- `lem-coef-sset-gluing-filtered-equivalences.json`

Every record has a sibling backup `<filename>.maint-Q26-cycle-1792204174.bak`. Existing-record backups precede the edits; the new core has a creation snapshot. Repositories: authoritative `/home/ubuntu/weil-conjectures-sheaf` and side `/home/ubuntu/weil-newtargets`. Both were repaired because `coord/dag-sync.md` identifies live DAG commits as authoritative and the side as a synced overlay. This prevents a later DAG sync from restoring the faulty prerequisite bindings.

The initial extraction/repointing was captured by the concurrent normal build snapshot commit `bda16b777fcc286b92ddaf3cdc43b41092628d72` (live), then imported by side sync commit `9a77531c25d32a34f3a253f07fb56cab9e325fee`. The final exact-path maintenance commits, made under `SHEAF_LEAD=L-only flock coord/.merge.lock` with `Bin Wu <844524296@qq.com>`, are live `782b5c96a8999b9960db00b37144330a669b3cf6` and side `168a5a6ec56dcd27bf5e8953039dd8be539a5bb7`. All four commits have the required identity. The final commits changed only the three remaining precision/report-field records because the rest was already committed by the normal snapshot/sync. No unrelated staged path was committed by this maintenance.

Independent reviewer `/root/review_cycle_repair` returned PASS after inspecting the full extraction and all changed proof/citation uses, arbitrary-source sharpness, strict cospan compatibility and preserved historical metadata. The original saved worker candidate over the repaired records has 148 reachable nodes and no cycle. All 19 supplied candidate citation quotes match after three mechanical bracket-ID quote refreshes by the parent maintenance agent.

Validation:

- Normal `tools/review_split.py` on the core and full Kan parent: PASS after committing the core. The precommit parent-only warning was the worker-new-child rule against an already split maintenance extraction, and disappears on the committed base.
- Full unmodified `tools/preflight_delivery.py Q26 lem-coef-quillen-b-comma-homotopy-fiber --base 168a5a6ec56dcd27bf5e8953039dd8be539a5bb7`: exit 0, `preflight OK: nothing the script can find; the mathematics is reviewed by the maintainer`.
- That full check ran in isolated server worktree `/tmp/q26-quillen-b-preflight-1792204174`, candidate-only detached commit `2a40da7df4`, with only the saved worker item and report layered on the repaired base. The commit was made under the side project's merge lock with the required identity. No branch was pushed and the original active worker sandbox/request was untouched.
- Full preflight log: `/tmp/q26-quillen-b-full-preflight-1792204174.log` on the server; also copied to the maintenance working directory as `full-preflight.log`.
- A raw whole-tree `check_dag.py --cycles` still prints three unrelated pre-existing cycles (14 nodes) and historical missing-dependency/blueprint/route/reach diagnostics. The normal full delivery preflight above performs its unchanged base-aware checks and passes; no Q26 cycle remains in the candidate's closure.
- No Lean files changed, so no Lean compile was needed. No lake build or process termination was performed.

The next worker should use a fresh shared snapshot based on side commit `168a5a6ec56dcd27bf5e8953039dd8be539a5bb7` or a descendant that includes it. The existing comma-fiber proof remains usable without mathematical changes. Any job whose delivery worktree was frozen before the repair may still report the old cycle; refresh its base by the normal pipeline. Continue the normal delivery/preflight path and do not suppress the cycle check or delete genuine prerequisites. The new core is a reviewed stage-1 split and can be stated later in the ordinary bottom-up stage-2 queue; no future Lean refactor was performed as part of this stage-1 repair.
