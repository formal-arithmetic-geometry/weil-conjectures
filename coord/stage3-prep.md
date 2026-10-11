# Stage 3 preparation (side copy; nothing switched)

Written 2026-10-11 by S3-W for L on the decision of the human (launcher 03:20 +08): "prepare stage 3 in a side copy, switch nothing". Stage 3 is **not** started. The live `lean/`, `tools/` and the stage-2 groups are untouched, and stage 2 continues. Sources: the reports of S3-A (library, build, queue, sync), S3-B (Challenge/TargetsCheck), S3-C (delivery, review, tools, brief) and S3-T (target review), all in L's scratchpad `$S/s3/` (`$S = /tmp/claude-1000/-home-ubuntu-cc1/b57befe1-7500-4e58-a9e1-bcb2c8a9c394/scratchpad`).

## 1. What is ready

| Piece | Where | State |
|---|---|---|
| Side copy | `~/weil-stage3-prep`, local branch `stage3-prep` (clone of sheaf-dag 5f4691816, `origin` removed, never pushed) | HEAD 6da3d4418 |
| One library | `lean/` = slopmaster2 `7d675a263` subtree-merged with full history (a75b79cbe; `blueprint` gitlink left out) + `lean/Sheaf` | `lean/lakefile.toml` = upstream's (package `weil-conjectures`, v4.33.1, same manifest) plus libs `Sheaf` (`globs = ["Sheaf.+"]`, `autoImplicit = false` on this lib only), `TargetsCheck`, `SheafChallenge` (roots `["Challenge"]`; the name `Challenge` is upstream's `Weil.Challenge`); defaultTargets `WeilConjectures, Challenge, Solution, Sheaf, TargetsCheck, SheafChallenge` (512e19c4d, aa9d6c1b9) |
| Config | side `coord/sheaf.env`: `SHEAF_LIB="WeilConjectures Sheaf"` (c724e7dc5) | |
| Build | `lake build` green, 12613 jobs; `tools/build.py` green | numbers in §2 |
| `lean/TargetsCheck.lean` | imports exactly `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper` (both target declarations) | 2e1c48405 (S3-B) |
| `lean/Challenge.lean` | the two target statements verbatim with `sorry`: `AlgebraicGeometry.Etale.isIso_baseChange_of_isProper`, `…_of_isProper_of_isAddTorsion_ring`; imports `BaseChange.Derived`, `BaseChangeTheorems.TorsionSheaf`, `Mathlib.Algebra.Category.ModuleCat.AB` (the last is needed: without its instance the elaborated types differ) | 2e1c48405 (S3-B) |
| `tools/target_types.sh check` | `cd ~/weil-stage3-prep && tools/target_types.sh check` → exit 0, "All 2 target statements agree with lean/Challenge.lean." (8.7 s) | passing |
| Target review | `coord/targets-review.md` (copied to the live coord/ with this file), reviewer S3-T (did not write the statements) | **ACCEPT WITH NOTES**, e35c648c2 |
| Import-direction check | side `tools/import_direction.py check` / `may <U> <S>` | 0 cycles |
| leanindex fix | side `tools/leanindex.py` reads `public/meta import [all]` | applied in side copy only |
| Tool drafts (stage 3 modes) | `$S/s3/C/patches/`: `stage3_delivery.new.patch`, `preflight_delivery.stage3.patch`, `review_packet.stage3.patch`, `merge_delivery.stage3.patch`, `review_class.stage3.patch`, `autoland.stage3.patch`; patched copies `$S/s3/C/draft-tools/`; tests `$S/s3/C/tests/` | apply cleanly (`patch --dry-run`) to live tools at 5f4691816; static checks tested on synthetic branches X1–X6, X8; the Lean-running parts (probe in `lean_file.sh`, `land.sh`/`land_set.sh` from the merge, AUTO kind check) untested until a library tree has stage 3 open |
| Worker brief | `coord/brief-stage3.md` (copied with this file, marked DRAFT) | not in force |
| Delivery form, review checklist, `coord/changes/` format | `$S/s3/C.md` | proposal |

Commits in the side copy: S3-A/S3-B/S3-T commits carry `Co-Authored-By: Claude Opus 5.5` (f4ea7ea90, a75b79cbe, 2e1c48405, 512e19c4d, aa9d6c1b9, c724e7dc5, e35c648c2), 6da3d4418 carries Fable 5.1, and three `build.py` commits (5014107dc, 130de4cf1, 9c5ed1754) carry none; 9c5ed1754 also swept S3-T's draft review (see §5).

## 2. The blocker and the facts that shape stage 3

### 2.1 Blocker: Lean's module system

All 1845 upstream files are `module`s; **1 of 2053** Sheaf files is (`Sheaf.AlgebraicGeometry.HomEtaleLocusTranslation`). Lean refuses `import` of a non-module file from a `module` (`error: cannot import non-`module` Sheaf.Algebra.Schanuel from `module``, tested with `public import` and plain `import`). So today **no upstream module can import a Sheaf module** (except that one), and "an upstream module may import Sheaf.*" does not hold as it stands. Options (a decision, §4):

| Option | What it means | Cost / effect |
|---|---|---|
| A. Convert the Sheaf closure needed to `module` | header `module`, `public import`, `@[expose] public section` in each Sheaf module an upstream proof needs, and in its whole Sheaf closure | changes what downstream modules may unfold; size depends on which Sheaf modules upstream proofs need |
| B. Move the needed Sheaf modules upstream | the planned `Sheaf.X -> WeilConjectures.X` rename, with a module header | same conversion per moved module; moves them out of `Sheaf/` |
| C. Keep upstream proofs free of Sheaf imports | upstream sorries are proved only from upstream + Mathlib; Sheaf stays on top | no conversion; Sheaf results cannot be used in the target's closure, which today is upstream only |

### 2.2 The queue (side copy, with the `public import` fix)

`SHEAF_LIB="WeilConjectures Sheaf" python3 tools/queue.py summary` (14 s): stage 3 library modules 3898; **needed by the targets 350**, outside 3548; **6 items** (all proof) and **3 waiting**. Without the fix the closure is 1 module.

| Order | Module | Distance | sorry |
|---|---|---|---|
| 1 | `…Etale.BaseChangeTheorems.Proper` | 0 | 1 |
| 2 | `…Etale.BaseChangeTheorems.ProjectiveLine` | 1 | 1 |
| 3 | `…Etale.BaseChangeTheorems.BaseChangeProperty` | 2 | 1 |
| 4 | `WeilConjectures.AlgebraicGeometry.Curve.FieldExtension` | 3 | 2 |
| 5 | `WeilConjectures.AlgebraicGeometry.Curve` | 4 | 1 |
| 6 | `…Etale.BaseChangeTheorems.DegreeZero` | 4 | 1 |
| waiting | `…ProjectiveLine.GeometricStalk` | 2 | on `prop-weil-pbc-strict-henselization-stalk-formula` |
| waiting | `…UnderivedExchange` | 3 | on the same node |
| waiting | `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar` | 5 | 2; on `lem-pc-base-change-map-cech`, `lem-sc-zariski-dimension-bound` |

The **five sorried declarations the targets rest on** are in **four modules**: FieldExtension, BaseChangeProperty, ProjectiveLine, GeometricStalk (waiting). The other queued modules hold sorries the targets do not use (the closure is per module, an upper bound): Proper l.157, Curve `genus_eq_finrankH_zero`, DegreeZero `isIso_globalSectionsUpperStarMap_of_henselianRing`, UnderivedExchange `isIso_baseChangeMap_of_isProper`, EulerChar (two). No Sheaf module is in the closure (§2.1). `dag_queue.py summary`: 223 stated modules waiting, 5850 nodes.

### 2.3 Build numbers (12 threads; all measured in the side copy)

| Step | Time | Modules built |
|---|---|---|
| Seed copy (`cp -a` slopmaster2 `.lake/build` + live Sheaf oleans; 7.9 GB) | 3 s | – |
| First `lake build` (one-time: the lake trace has `Package.id` `sheaf-weil` → `weil-conjectures`) | **527 s** | 2054 (2053 Sheaf + TargetsCheck); 0 upstream, 0 Mathlib |
| `tools/build.py` on a fresh `local/buildtree` | 17 s (lake 10 s) | 2 |
| Incremental: comment appended at end of `Curve/FieldExtension` | 11 s | 1 |
| Incremental: comment inside a proof of `Curve/FieldExtension` (later lines shift) | **21 s** | 2 (FieldExtension, TargetsCheck); none of the 88 downstream upstream modules |

A proof-only change in a `module` leaves its public `.olean` unchanged; non-module files (TargetsCheck, every Sheaf module) rebuild on any change in their closure. A from-scratch build of the whole library (~1845 upstream + 2053 Sheaf) was not measured. Renaming the package instead would rebuild the upstream side.

### 2.4 Import direction

446 Sheaf modules import 156 distinct upstream modules directly; the Sheaf closures contain **979 upstream modules** ("below Sheaf"); no upstream module imports Sheaf; **0 cycles**. Rule (`tools/import_direction.py`): an upstream module U may import a Sheaf module S only if U is not in the import closure of S. Commands: `python3 tools/import_direction.py check` (exit 1 on a cycle), `python3 tools/import_direction.py may <U> <S>` (exit 0 allowed, 3 would close a cycle). `import_prune_check.py` check 4 enforces it at landing once leanindex reads `public import`.

### 2.5 Hollow definitions

`tools/hollow_defs.sh` (side copy, SHEAF_LIB in `coord/sheaf.env`): **1102 definitions scanned, 0 candidates**, 5 s. It covers what TargetsCheck reaches, upstream only today.

### 2.6 Upstream sync after a switch

`git fetch <upstream> slopmaster2 && git subtree merge --prefix=lean FETCH_HEAD -m "Sync lean/ with slopmaster2 <sha>"` (or `git merge -X subtree=lean FETCH_HEAD`), then `lake build`, a new sorry map, `lean_status.py`.

| Measure | Full history | Squash |
|---|---|---|
| Repository size (62.8 MiB now) | 82.2 MiB (**+19.4 MiB**, +31 %) | 68.5 MiB (**+5.7 MiB**) |
| One sync of 707 commits (71d63dcf6 → 7d675a263) | +2.6 MiB | +1.5 MiB |
| Merge time | < 1 s | < 1 s |

Conflicts expected only in `lean/lakefile.toml` (our three libs) and the deleted `blueprint` gitlink if upstream bumps it (neither changed in those 707 commits). Squash needs the first add made by `git subtree add --squash`; the side copy used full history. A Mathlib bump in upstream's manifest would need a packages directory of our own (today the shared one is slopmaster2's).

## 3. What a switch would do, and how long it stops the groups

Steps, on `sheaf-dag` in the live repository (not done):

1. Stop `~/cc1/buildloop.sh` and `~/cc1/autoland.py`; let running merges finish under `coord/.merge.lock`; announce the stop in STATE.
2. Replace `lean/` by the side copy's layout: remove `lean/{lakefile.toml,lake-manifest.json,lean-toolchain}`, subtree-merge slopmaster2 `7d675a263` (as a75b79cbe), add the three libs to `lean/lakefile.toml` (as 512e19c4d, aa9d6c1b9), add `lean/TargetsCheck.lean` and `lean/Challenge.lean`, set `SHEAF_LIB="WeilConjectures Sheaf"` in `coord/sheaf.env`; keep the packages link.
3. Rebuild the Sheaf side once under the new package name: either `lake build` in place (527 s), or build the side copy beforehand while stage 2 runs, then re-seed `lean/.lake/build` from it (3 s copy) and rebuild only the Sheaf modules landed since.
4. Refresh `local/buildtree` and the L compile mirror `local/build/L` (`tools/build.py` once: 17 s fresh); the base move of 15:52 showed the mirror must be refreshed too.
5. The remote machines' library copies follow on their refresh (every 2 min, per the launcher).
6. Apply the tool patches (`$S/s3/C/patches/`, plus the §5 fixes) and re-point `autoland.py`/`buildloop.sh` (same repository and branch; `autoland` passes `--stage 3` for module items).
7. `python3 tools/queue.py write` for stage 3 (summary 14 s), STATE line `STAGE 3 READY`, `coord/brief-stage3.md` in force.

Estimated stop of the groups' compiles and landings:

| Step | Rebuild in place | Pre-built and re-seeded | Basis |
|---|---|---|---|
| 1 stop loops, drain merges | 1–2 min | 1–2 min | estimated |
| 2 subtree merge + lakefile + sheaf.env, commit | ~1 min | ~1 min | merge < 1 s measured (sync); rest estimated |
| 3 Sheaf rebuild | **8.8 min** (527 s) | 3 s copy + 1–3 min for Sheaf modules landed since | 527 s, 3 s measured; catch-up estimated |
| 4 build.py / mirror | 0.3 min | 0.3 min | 17 s measured |
| 5 remote copies | ≤ 2 min | ≤ 2 min | launcher's period |
| 6 tool patches + a smoke test | 5–10 min | 5–10 min | estimated (patches apply cleanly, measured) |
| 7 queue write | 0.3 min | 0.3 min | 14 s measured (summary) |
| **Total** | **~19–25 min** | **~11–19 min** | |

Step 6 can be done before the stop on a tools branch if the patches are first tested in the side copy; the stop is then ~13–15 min (in place) or ~5–9 min (re-seeded). Stage-2 deliveries in flight touch only `lean/Sheaf`, node files and reports, so they stay mergeable across the switch; they cannot compile during step 3.

## 4. Open decisions for the human

1. **Module-system blocker** (§2.1): A convert the needed Sheaf closure to `module`; B move the needed Sheaf modules upstream (`Sheaf.X -> WeilConjectures.X`); C keep upstream proofs free of Sheaf imports. Waits: whether any Sheaf result can serve the targets.
2. **Library proof route of target 1** (targets-review open point 1): it goes through `hasTorsionBaseChange_of_hasInjectiveAcyclicity` (`ProjectiveLine.lean:121`), believed false for general Λ (HUMAN.md, counterexample Λ = ℤ[x₁,x₂,…]/(pⁱxᵢ, xᵢxⱼ)). Either prove through a ℤ-only (or torsion-Λ) route plus restriction of scalars / the human's fix (b) `IsAddTorsion Λ` or (d) for that lemma, or restrict the target to ℤ (then `Challenge.lean` and the library declaration change, `AGENTS.md` §4).
3. **Second target** (open point 2): `…_of_isAddTorsion_ring` is extra, not a clause of the node, implied by the first; recommendation keep; its `@[stacks 095T]` should read 0DDE / SGA 4 XII 5.1 for torsion Λ.
4. **Λ = ℤ via `ULift ℤ`** (open point 3): the equivalence `ModuleCat (ULift ℤ) ≌ AddCommGrpCat` is not formalised; accept as is?
5. **Re-review on definition changes** (open point 4): the review holds only while `derivedBaseChangeMapPlus`, `baseChangeMap`, `upperStar`/`lowerStar`, `IsTorsionSheaf`, `torsionHomology` are unchanged.
6. **Comparator configuration** (open point 5, S3-B): solution module (`TargetsCheck` the natural one) and where its config lives; the contract does not say.
7. **Upstream sorries outside the queue vs the comparator** (C question 11): `queue.py` scans `SHEAF_LIB`; with `WeilConjectures` added the six items are upstream modules. Who proves upstream sorries, and do they go into the queue as items of our groups? The comparator refuses the library while any stays reachable from a target.
8. **Tiered review for stage 3** (human's proposal; AUTO = proofs only, compiles, no new unnoded `sorry`, no axiom; FULL = statement, definition, visible import, or nodes): spec and patch in `$S/s3/C.md`. Its 12 questions:
   1. Does `TargetsCheck`/`Challenge` count as an importer? (draft: no)
   2. Added proof-dependency imports and removed unused imports: AUTO when `import_prune_check` passes? (357 of 2053 Sheaf modules have importers)
   3. Is a new public sorry-free helper lemma "adding a node"? (draft: public → FULL, private → AUTO)
   4. Proof-only change in a target module: AUTO or always FULL?
   5. A sample (stage 2: one in four) for stage 3? (draft: none)
   6. A `coord/repairs.txt` repair: AUTO or FULL? (draft: AUTO)
   7. DAG drift when an AUTO proof takes a shorter route than `proof_deps`: accept, or require the node update (FULL)?
   8. New fields: `STAGE3_OWNS` (`lean`, `proof`, `proof_deps`, `proof_origin` + statement fields under §3), `reviewed_proof`, and a `pruned` {date, why} record for a pruned module's node.
   9. Allow `claim.py take` for remote groups to claim adapted modules (§3.1)?
   10. Adopt the newer SHEAF template's stage-3 points (proof landing not recompiled; `claim.py next --after`; helper-lemma rule) or run strictly on the project's copy?
   11. Upstream sorries vs the comparator (item 7 above).
   12. Keep `## Second reading by <G>` in the stage-3 report (not in `worker.md` §3)?
9. **`coord/changes/` format** (`$S/s3/C.md`): `# <declaration>`, `## Reason`, `## Old`, `## New`, `## Users` (module | group | effect), `## Status` open → landed <id> → closed <build commit> | reverted; the lead closes after the green build; no tool yet.
10. **Squash or full history** for the subtree (§2.6: +5.7 vs +19.4 MiB).
11. **Attribution of the side-copy commits**: seven carry `Co-Authored-By: Claude Opus 5.5` (one Fable 5.1, three build commits none). Keep, or rewrite to the run's attribution before anything from the side copy lands on sheaf-dag?

## 5. Tool gaps found (live tools untouched)

| Tool | Gap | Fix proposed |
|---|---|---|
| `tools/leanindex.py:146` `_IMPORT`, `tools/stage2_delivery.py:184` | `^import\s+…` misses `public import` / `meta import` / `import all` (7854 upstream lines): queue closure 1 instead of 350; `import_prune_check` blind for upstream | `r"^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.']+)"` (applied in the side copy); `interface()` over-reports, which is safe |
| `tools/sheaf_env.sh` | sources `coord/sheaf.env` after the environment, so `SHEAF_LIB=… tools/hollow_defs.sh` is overridden (0 definitions scanned); Python `config()` lets the environment win | set it in `coord/sheaf.env`, or source the file only for unset variables |
| `tools/build.py` `commit_tree` | `git add -A` commits other agents' uncommitted files (swept S3-T's review into 9c5ed1754 and a test edit) | by design on live ("commit the tree"); revert test edits from a saved copy, or restrict the add |
| `tools/lean_file.sh` (`SHEAF_LEAN_OPTS`) | reads only the package `[leanOptions]`; the `Sheaf` library's `autoImplicit = false` is not applied to single-file compiles, so a file can compile alone and fail in the global build | parse the `Sheaf` lib's `leanOptions` too, or drop `autoImplicit=false` (upstream uses only `relaxedAutoImplicit=false`); package level would rebuild upstream |
| `tools/compile_remote.sh` | rejects `.` in the item, and stage-3 items are module names | allow dots, or the brief's workaround (`_` for `.`) |
| `tools/preflight_delivery.py`, `review_packet.py`, `merge_delivery.py`, `review_class.py`, `~/cc1/autoland.py` | no stage-3 mode | drafts in `$S/s3/C/patches/` |
