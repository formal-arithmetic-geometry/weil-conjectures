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

## Addendum (03:30 +08): the five upstream sorries against their nodes; the four nodes without Lean

Written 2026-10-11 by S3-D for L. Read-only: slopmaster2 `7d675a263` (`~/weil-conjectures-slopmaster2`), the sorry map `local/sorry_map_slopmaster2_7d675a26.jsonl.gz`, the node files in `dag/nodes/sec-proper-base-change/`, `coord/HUMAN.md` (entries of 2026-10-09 evening and 2026-10-10 10:14) and Stacks `etale-cohomology.tex` §59.91.

### 0. Pairing confirmed

Each pair below appears in the node's `lean` record (module, declaration, line). The sorry map gives each of the five declarations its own `sorry` (`s = true`).

| Node | Upstream declaration | Module : lines |
|---|---|---|
| lemma-weil-pbc-p1-exchange-geometric-stalk | `Etale.exists_addEquiv_sheafFiber_baseChangeHomologyMap_projectiveLine` | `…BaseChangeTheorems.ProjectiveLine.GeometricStalk` : 93–159 |
| lemma-weil-pbc-property-iff-acyclicity (record also lists the three sorry-free `HasTorsionBaseChange.hasInjectiveAcyclicity`, `HasInjectiveAcyclicity.hasTorsionBaseChange`, `hasTorsionBaseChange_iff_hasInjectiveAcyclicity`) | `Etale.hasTorsionBaseChange_of_hasInjectiveAcyclicity` | `…BaseChangeTheorems.BaseChangeProperty` : 309–323 |
| lem-weil-pbc-injective-acyclicity-bounded-below | same | same |
| prop-weil-pbc-reduction-to-projective-line | `Etale.hasTorsionBaseChange_of_projectiveLine_of_isProper` | `…BaseChangeTheorems.ProjectiveLine` : 124–149 |
| prop-weil-pbc-algebraically-closed-extension | `IsCurve.bijective_cohomologyMap_of_isAlgClosed` | `WeilConjectures.AlgebraicGeometry.Curve.FieldExtension` : 69–95 |
| lemma-weil-pbc-curve-separably-closed-passage | `IsCurve.bijective_cohomologyMap_of_isSepClosed_of_isAlgClosed` | same : 97–134 |

The Lean route of target 1 is: `isIso_baseChange_of_isProper` → `hasTorsionBaseChange_of_isProper` → `hasTorsionBaseChange_of_projectiveLine_of_isProper` (sorry), applied to `hasTorsionBaseChange_projectiveLine`. That declaration is `hasTorsionBaseChange_of_hasInjectiveAcyclicity` (sorry) applied to `hasInjectiveAcyclicity_projectiveLine`. That in turn is `isIso_baseChangeHomologyMap_projectiveLine`, which uses `exists_addEquiv_…` (sorry) and `bijective_cohomologyMap_of_isSepClosed`. The last is the two curve sorries. Target 2 (`…_of_isAddTorsion_ring`) is target 1 together with `torsionHomology_of_isTorsion`.

### Encoding gaps shared by all five (referred to as G1–G6 below)

| | Lean (all five) | Nodes | Bridge needed |
|---|---|---|---|
| G1 coefficients | `Sheaf X.smallEtaleTopology (ModuleCat.{u+1} Λ)`, with `Λ : Type (u+1)` any `CommRing`. `R+`, `upperStar` and the exchange map are computed in Λ-modules | abelian sheaves `Ab(X_et)` (`Sheaf … AddCommGrpCat.{u+1}`). The Sheaf records `HasTorsionAbelianBaseChange` and `HasPrimeInjectiveAcyclicity` are abelian | `forget₂ (ModuleCat Λ) AddCommGrpCat` commutes with `upperStar`, with `R+ lowerStar` on D⁺ (Λ-injectives are acyclic for the abelian `f_*`), and with the exchange map; it is also conservative. There is **no node** for this (lead_note of 2026-10-10 on lem-weil-pbc-injective-acyclicity-bounded-below). The nearest upstream statement is the change of rings in `Etale.isIso_baseChangeHomologyMap_of_nsmul_eq_zero` (SmoothBaseChange/Coefficients.lean:133, which has its own sorry) |
| G2 torsion | `Scheme.IsTorsionSheaf` (geometric stalks are torsion groups); `torsionHomology` (every homology sheaf is `IsTorsionSheaf`) | def-weil-pbc-torsion-etale-sheaf = Sheaf `Scheme.IsTorsionAbelianSheaf` (`colim F[n] → F` is an iso) | `IsTorsionSheaf F ↔ IsTorsionAbelianSheaf (forget F)`. Ingredients: upstream `Scheme.isTorsionSheaf_iff_isTorsion` (sorry-free) and lem-weil-pbc-torsion-sheaf-characterizations |
| G3 cohomology | `Sheaf.H` (Ext from the constant sheaf ℤ) and `Etale.cohomologyMap` | def-weil-pbc-etale-cohomology = `Etale.cohomology` (RΓ via K-injectives). def-weil-pbc-cohomology-pullback = `Etale.cohomologyMap` (on `Sheaf.H`). The DAG mixes the two | `Sheaf.H F q ≅ (Etale.cohomology … q).obj F[0]`, natural in F and compatible with pullback. Needed wherever a node computes `H^q` by resolutions or cochains |
| G4 squares | any `IsPullback` square (arbitrary `X'`/`C'`) | the canonical fibre product (`X' = P¹_T`, `C_{k'} = C ×_k k'`) | transport along the unique isomorphisms. Routine, but every proof needs it |
| G5 exchange map | `derivedBaseChangeMapPlus`, or `Etale.baseChange` through `baseChangeHomologyMap` | def-weil-pbc-derived-exchange (records both) | `baseChange_eq_derivedBaseChangeMapPlus` (sorry-free). No gap |
| G6 sheaves vs complexes | `HasTorsionBaseChange Λ f`: K ∈ D⁺(X, Λ) with torsion cohomology | `PBC(f)` (def-weil-pbc-property): a torsion abelian sheaf in degree 0 | the 0DDE spectral-sequence passage: steps 4–7 of thm-weil-pbc-bounded-below, which are steps 2–6 of lem-weil-pbc-injective-acyclicity-bounded-below |

Universes match throughout: schemes are `Scheme.{u}`, fields are `Type u`, and coefficients live in `u+1`. The Sheaf IA record takes `ULift (ZMod r)` for 𝐅_r. Neither side has a universe obstruction.

### 1. `Etale.exists_addEquiv_sheafFiber_baseChangeHomologyMap_projectiveLine` ↔ lemma-weil-pbc-p1-exchange-geometric-stalk

**Lean** (GeometricStalk.lean:133):
```lean
theorem Etale.exists_addEquiv_sheafFiber_baseChangeHomologyMap_projectiveLine
    {S T X' : Scheme.{u}} {g : T ⟶ S} {f' : X' ⟶ T} {g' : X' ⟶ ProjectiveLine S}
    (sq : IsPullback g' f' (ProjectiveLine S ↘ S) g)
    {k k' : Type u} [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k']
    (σ : Spec (.of k) ⟶ S) (τ : Spec (.of k') ⟶ T) (ι : Spec (.of k') ⟶ Spec (.of k))
    (hι : ι ≫ σ = τ ≫ g)
    (hσ : ∃ (s : S) (φ : S.residueField s ⟶ .of k), φ.hom.IsIntegral ∧ Spec.map φ ≫ S.fromSpecResidueField s = σ)
    (hτ : ∃ (t : T) (φ : T.residueField t ⟶ .of k'), φ.hom.IsIntegral ∧ Spec.map φ ≫ T.fromSpecResidueField t = τ)
    (F : Sheaf (ProjectiveLine S).smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsTorsionSheaf F] (q : ℕ) :
    ∃ (e₁ : (stalk at τ of (baseChangeSourceFunctor Λ g p q).obj F) ≃+ Sheaf.H (forget ((map σ)^*[Λ] F)) q)
      (e₂ : (stalk at τ of (baseChangeTargetFunctor Λ g' f' q).obj F) ≃+ Sheaf.H ((map ι)^*[Ab] (forget ((map σ)^*[Λ] F))) q),
      ∀ x, e₂ (stalk map of (baseChangeHomologyMap Λ sq q F) x) = Etale.cohomologyMap (map ι) (forget ((map σ)^*[Λ] F)) q (e₁ x)
```
(Abbreviated: "stalk at τ" is `(pointSmallEtale τ).sheafFiber (A := ModuleCat Λ)`, `forget` is `sheafCompose _ (forget₂ (ModuleCat Λ) AddCommGrpCat)`, and `map` is `ProjectiveSpace.map _`.)

**Node:** `X = P¹_S`, `X' = P¹_T`, and F is a torsion abelian sheaf on X_et. There is one geometric point t̄ : Spec Ω → T, and s̄ = g∘t̄. The fields are κ(s̄) ⊂ κ(t̄), the separable closures of κ(s), κ(t) in Ω. A = O^sh_{S,s̄}, B = O^sh_{T,t̄}. Claims: (1) c_S = i_A^*Φ_Sσ and c_T = i_B^*Φ_T are isomorphisms; (2) Φ_T∘(Ex^q)_t̄ = h̃^*∘Φ_S∘σ; (3) c_T∘(Ex^q)_t̄ = h_0^*∘c_S.

| Clause | Lean vs node |
|---|---|
| square | Lean allows any pullback (G4); the node fixes X' = P¹_T. Equivalent |
| P¹ | `ProjectiveLine S = ℙ(ULift (Fin 2); S)` against `P({0,1};S)` (recorded as `ProjectiveSpace`). Same |
| sheaf | Lean: a Λ-module sheaf with torsion stalks. Node: a torsion abelian sheaf. Modulo G1/G2 the Lean covers a sub-class (sheaves of the form `forget F`), so it is **weaker** here |
| geometric points | Lean: σ and τ are *independent* separably closed points, **algebraic** over κ(s) and κ(t) (not necessarily the separable closures: the only caller passes `AlgebraicClosure`), linked by an arbitrary ι with `ι ≫ σ = τ ≫ g`. Node: one point Ω with κ(s̄) = κ(s)^sep in Ω. Lean is **more general** here |
| stalk | `(pointSmallEtale τ).sheafFiber`, which is the record of def-weil-pbc-geometric-stalks. Same, modulo G1 |
| source/target | Lean: homology of `R+ p_*` in Λ-modules, then `g^*`, taken in Λ-modules (G1). Node: abelian `R^q p_*` |
| cohomology | Lean: `Sheaf.H` and `cohomologyMap`. Node: H^q via RΓ (G3) |
| conclusion | Lean: *there exist* additive equivalences e₁, e₂ making the square commute; it does not ask for them to be canonical. Node: the specific c_S, c_T. Lean is **weaker** (its docstring says so). Under the sorry-free `isIso_baseChangeHomologyMap_projectiveLine`, the Lean form is equivalent to bijectivity of the stalk map |

**Does the node's proof prove the Lean?** Mostly. Claim (3) of the node gives the Lean square for Ω = k', k = κ(s)^sep and k' = κ(t)^sep. Five things are missing:
1. G1 on both sides: the Λ-stalk of `H^q(g^*R+p_*F[0])` must be identified with the stalk of the abelian `g^{-1}R^q p_*(forget F)`, and likewise on the target side. The node's Steps 2–4 run on abelian injective resolutions.
2. G3: the codomains of c_S and c_T must be read as `Sheaf.H`, with h_0^* = `cohomologyMap`.
3. The purely inseparable gap: the Lean k may be strictly larger than κ(s)^sep. One extra step is needed: `H^q(P¹_{κ(s)^sep}) → H^q(P¹_k)` is bijective because the base change is a universal homeomorphism (upstream `Etale.cohomologyMap_bijective`, sorry-free; DAG prop-weil-pbc-universal-homeomorphism-topos). The same holds for k', together with commutativity of the resulting square.
4. Aligning the independent σ with the node's s̄ = g∘t̄. The separable closure of κ(s) in k maps by ι onto the separable closure of κ(s) in k'. The argument is the one in lem-weil-pbc-strict-henselization-functoriality (2), but the Lean form needs it written out.
5. G4: the Lean target sheaf is `(map ι)^*[Ab](forget((map σ)^*[Λ] F))`. That needs the composite-inverse-image isomorphisms and the commutation of `forget` with `upperStar` (not found upstream by grep).

None of the node's steps fails. The node's review already flags a "hypothesis gap" in prop-weil-pbc-p1-strict-henselian-comparison, which is the node's own business.

### 2. `Etale.hasTorsionBaseChange_of_hasInjectiveAcyclicity` ↔ lem-weil-pbc-injective-acyclicity-bounded-below and lemma-weil-pbc-property-iff-acyclicity

**Lean** (BaseChangeProperty.lean:321):
```lean
variable (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}
theorem Etale.hasTorsionBaseChange_of_hasInjectiveAcyclicity (f : X ⟶ Y) [IsProper f]
    (hf : Etale.HasInjectiveAcyclicity Λ f) : Etale.HasTorsionBaseChange Λ f := sorry
-- HasTorsionBaseChange Λ f := ∀ sq : IsPullback g' f' f g, ∀ K : D⁺(Sheaf X_et (ModuleCat Λ)),
--   torsionHomology Λ X K → IsIso ((derivedBaseChangeMapPlus (ModuleCat Λ) sq.toCommSq).app K)
-- HasInjectiveAcyclicity Λ f := ∀ sq, ∀ I : Sheaf X_et (ModuleCat Λ), IsTorsionSheaf I → Injective I →
--   ∀ q > 0, IsZero (H^q (R+ (f')_*[ModuleCat Λ] ((g')^*[ModuleCat Λ] I)[0]))
```

**Node lem-weil-pbc-injective-acyclicity-bounded-below** (after the statement_change of 2026-10-11): Λ is any commutative ring and f is proper. The hypothesis is coefficient-wise IA: for every prime ℓ, every square and every injective sheaf I of (Λ/ℓ)-modules, `R^q f'_* g'^{-1} I = 0` for q > 0, with the abelian `R^q` of the underlying abelian sheaf. Conclusion: for K ∈ D⁺(X_et, Λ) with torsion cohomology, the **abelian** exchange `Ex_{□,K}` is an isomorphism in D⁺(Y'_et).

| Clause | Lean vs node |
|---|---|
| Λ, f proper, all squares | same |
| hypothesis: injectives | Lean: injective objects of Λ-module sheaves that are torsion. Node: injective (Λ/ℓ)-module sheaves, for every prime ℓ. **Different, and neither implies the other** (statement_change 2026-10-11, checker R-e7c0032; HUMAN.md 10-10: a Λ/ℓ-injective is a summand of I[ℓ] for a Λ-injective I that need not be torsion) |
| hypothesis: R^q | Lean: in Λ-modules (`R+` of `ModuleCat Λ`). Node: abelian. Re-encoded (G1) |
| conclusion | Lean: iso in D⁺(Y', Λ). Node: iso of the underlying abelian complexes. The node plus G1 gives the Lean conclusion |
| torsion of K | `torsionHomology` against "cohomology sheaves torsion as abelian sheaves". Same modulo G2 |

**Does the node's proof prove the Lean?** **No.** Step 1 cites lem-weil-pbc-arbitrary-ring-torsion-sheaf-base-change, whose hypothesis is the coefficient-wise IA. The Lean `hf` does not supply it. Steps 2–6 (the 0DDE truncation spectral sequences) do carry over, because they use only the sheaf case. The HUMAN.md addendum of 2026-10-10 shows that the 0A4B route cannot start from the Lean hypothesis: a torsion Λ-sheaf need not embed in a torsion injective, with Λ = ℤ[x₁,x₂,…]/(pⁱxᵢ, xᵢxⱼ). The Lean statement is nonetheless **true** for proper f, because its conclusion is target 1. Its only known proof goes through the target, which is a cycle on the present route, since `hasTorsionBaseChange_projectiveLine` uses it.

**Node lemma-weil-pbc-property-iff-acyclicity:** for proper f, PBC(f) (torsion abelian sheaves in degree 0; Sheaf `HasTorsionAbelianBaseChange`) holds iff IA_r(f) for every prime r (𝐅_r-injectives; Sheaf `HasAllPrimeInjectiveAcyclicity`). Against the Lean, this is an iff where the Lean has one direction. It is abelian where the Lean uses Λ, sheaves where the Lean uses complexes, and 𝐅_r-injectives where the Lean uses torsion-Λ injectives. The node's proof (Stacks 0A4B) proves the abelian iff, **not** the Lean declaration. The pairing is nominal. The node's natural Lean is a Sheaf theorem `hasTorsionAbelianBaseChange_iff_hasAllPrimeInjectiveAcyclicity [IsProper f]`; the forward half already exists as the Sheaf `hasAllPrimeInjectiveAcyclicity_of_hasTorsionAbelianBaseChange`. Its `lean.declarations` should drop the upstream sorry.

**What stage 3 needs.** This is a decision, and it is still open: HUMAN.md 10-09 evening and 10-10 10:14, and stage3-prep §4 item 2.
- **(b)** Add `IsAddTorsion Λ`. The declaration then becomes the sorry-free `HasInjectiveAcyclicity.hasTorsionBaseChange`. That proof calls `Etale.isIso_baseChangeMap_of_isProper` (UnderivedExchange.lean:52, **its own sorry**; node lemma-weil-pbc-proper-underived-exchange), which adds a **sixth** sorry to the route. Target 1 for general Λ then needs another way in (restriction of scalars).
- **(d)** Restate `HasInjectiveAcyclicity` coefficient-wise (Λ/ℓ-injectives, every ℓ). The node then proves the declaration once G1 is in place. `hasInjectiveAcyclicity_projectiveLine` must be re-proved: it needs `R^q p_* I = 0` (Λ-derived) for a Λ/ℓ-injective I, a change of rings with no node yet.
- **(c′, recommended)** Re-prove the sorry-free `hasTorsionBaseChange_projectiveLine` (ProjectiveLine.lean:119–122) directly. Use the sorry-free `isIso_baseChangeHomologyMap_projectiveLine`, which gives the degree-q exchange iso for every torsion Λ-sheaf, plus the Λ-typed 0DDE lift (steps 2–6 of this node). No IA is needed. The declaration then leaves the target's closure; it could later be closed from `hasTorsionBaseChange_of_isProper` if moved after it. This is a proof-only change of an upstream module.

### 3. `Etale.hasTorsionBaseChange_of_projectiveLine_of_isProper` ↔ prop-weil-pbc-reduction-to-projective-line

**Lean** (ProjectiveLine.lean:145):
```lean
theorem Etale.hasTorsionBaseChange_of_projectiveLine_of_isProper
    (h : ∀ S : Scheme.{u}, Etale.HasTorsionBaseChange Λ (ProjectiveLine S ↘ S))
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] : Etale.HasTorsionBaseChange Λ f := sorry
```
**Node:** if `P¹_S → S` satisfies PBC for every scheme S, then every proper f satisfies PBC. PBC is abelian, for torsion sheaves in degree 0.

| Clause | Lean vs node |
|---|---|
| coefficients | Λ against ℤ (G1), in both the hypothesis and the conclusion |
| objects | complexes with torsion cohomology against sheaves in degree 0 (G6), in both the hypothesis and the conclusion |
| P¹, properness, universes | same |
| logical strength | **Re-encoded, not comparable.** The Lean hypothesis (Λ-complexes) does not give the node's abelian hypothesis; for Λ = ℚ it is vacuous. The converse fails too |

**Does the node's proof prove the Lean?** In shape yes (Stacks 0A4F: affine base, Chow, closed immersions are finite, ℙ¹ → ℙⁿ, composition, cancellation), but not as written. Six of its citations are typed for abelian PBC/IA and need Λ-complex versions:
- target locality: Sheaf `hasTorsionAbelianBaseChange_of_etale_cover`
- lem-weil-pbc-reduction-projective-space
- prop-weil-pbc-composition-stability
- lemma-weil-pbc-cancellation
- lemma-weil-pbc-property-iff-acyclicity
- prop-weil-pbc-finite-morphism

Some of the pieces already work for Λ:
- Finite morphisms: upstream `isBaseChangeIso_of_isFinite` (any coefficient) with `hasTorsionBaseChange_of_isBaseChangeIso`, both sorry-free.
- Chow's lemma: Sheaf `exists_chow_factorization_of_isAffine` (coefficient-free; upstream `ChowModification` is Noetherian only, as the docstring notes).
- Composition, for complexes: pasting the derived exchange (lem-weil-pbc-exchange-identity-pasting), plus the fact that Rf'_* keeps torsion cohomology. No IA is needed.
- Cancellation: this does need IA, in the Λ/ℓ form of (d).

The alternative is to prove the conclusion unconditionally and ignore `h`, since the statement is a true theorem. That would use the abelian DAG route plus G1 and the G6 lift. The abelian ℙ¹ case would then come from the DAG, and under stage3-prep §2.1 option C that means Sheaf imports in an upstream proof, which are not available.

### 4. `IsCurve.bijective_cohomologyMap_of_isAlgClosed` ↔ prop-weil-pbc-algebraically-closed-extension

**Lean** (FieldExtension.lean:88):
```lean
theorem bijective_cohomologyMap_of_isAlgClosed {k k' : Type u} [Field k] [IsAlgClosed k]
    [Field k'] [IsAlgClosed k'] {C C' : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f]
    [IsProper f] {ι : Spec (.of k') ⟶ Spec (.of k)} {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C}
    (h : IsPullback ι' f' f ι) (F : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsTorsionSheaf F] (q : ℕ) :
    Function.Bijective (Etale.cohomologyMap ι' ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) q)
```
**Node:** k ⊆ k' are algebraically closed; C is proper over k with dim C ≤ 1 (the empty scheme is allowed); F is a torsion abelian sheaf. Then `π^* : H^q(C,F) → H^q(C_{k'}, π^{-1}F)` is an isomorphism (Stacks 03SC (7)).

| Clause | Lean vs node |
|---|---|
| fields, ι | algebraically closed in both. Lean takes any morphism ι, which is always induced by k → k'. Same |
| curve | `IsCurve f` (separated, locally of finite type, quasi-compact, `topologicalKrullDim C ≤ 1`) plus `IsProper f`, against "proper with dim ≤ 1, empty allowed". Same (proper implies separated and finite type; ⊥ ≤ 1 covers the empty scheme) |
| square | any pullback (G4) |
| sheaf | `forget F` for a Λ-sheaf with torsion stalks, against any torsion abelian sheaf. **Lean weaker** (a special case, given G2) |
| cohomology, map | `Sheaf.H` and `cohomologyMap`, against H^q and π^* (G3; the pullback record is already `cohomologyMap`) |
| conclusion | bijective against isomorphism. Same |

**Does the node's proof prove the Lean?** **Yes.** Apply the node to the abelian sheaf `forget F`; the needed facts are `IsTorsionSheaf F ⇒ IsTorsionAbelianSheaf (forget F)` (G2) and the G4 transport. The node's dévissage (F[ℓ], j_!, constructible 𝐅_ℓ-sheaves, normalisation) runs entirely on abelian sheaves, which is legitimate because the Lean instance is the abelian sheaf `forget F`. G3 matters only where a step of the subtree computes H^q by resolutions. The upstream curve files (`Curve/*.lean`) use `Sheaf.H`, so that subtree is probably consistent already.

### 5. `IsCurve.bijective_cohomologyMap_of_isSepClosed_of_isAlgClosed` ↔ lemma-weil-pbc-curve-separably-closed-passage

**Lean** (FieldExtension.lean:120): the separably closed version of §4, under a hypothesis `H` that is exactly the statement of §4 for the **same Λ**. `H` quantifies over k, k' : Type u, C : Scheme.{u}, Λ-module torsion sheaves and any pullback square.

**Node:** k ⊆ k' are separably closed. Hypothesis (H) covers all algebraically closed K ⊆ K', all proper D with dim ≤ 1, and **all torsion abelian sheaves** G. The conclusion is π^* bijective (Stacks 0A5E).

| Clause | Lean vs node |
|---|---|
| hypothesis H | Lean: only for sheaves `forget G` with G a torsion Λ-sheaf. Node: all torsion abelian sheaves. **Lean hypothesis weaker** |
| conclusion | only for Λ-sheaves. **Lean conclusion weaker** |
| fields, curve, square, cohomology | as in §4 |

**Does the node's proof prove the Lean?** **Yes**, with two small additions:
- **Where H is used.** The node applies (H) to G = F (characteristic 0, step 1) and to G = ρ^{-1}F (step 6). In Lean, take `ρ^*[Λ] F` instead. It is torsion by the upstream instance `isTorsionSheaf_upperStar` (TorsionSheaf.lean:153). Transport along `forget ∘ ρ^*[Λ] ≅ ρ^*[Ab] ∘ forget` (not found upstream by grep; this is a sheaf-level piece of G1), using naturality of `cohomologyMap` in the sheaf (TopologicalInvariance.lean, sorry-free).
- **Hypotheses of H.** The node's step 6 supplies `IsCurve` for `C_{k̄} → Spec k̄` (base change keeps separated, locally of finite type and quasi-compact; the dimension is preserved by the homeomorphism).

Step 5 of the node is upstream `Etale.cohomologyMap_bijective` (sorry-free). No step fails.

### 6. The four nodes between the target and the five, with no upstream Lean

The upstream Lean has no declaration for any of them. ProjectiveLine.lean says: "The reduction also absorbs several steps which the blueprint keeps separate — target locality, stability under composition, and cancellation along a proper surjection (Stacks 0A4D and 0A4C) — none of which is stated on its own here." Each has a stage-2 **Sheaf** record. These records are abelian, carry a `sorry`, and are statement-only.

| Node (Sheaf record) | Upstream Lean | Verdict |
|---|---|---|
| prop-weil-pbc-composition-stability (`prop_weil_pbc_composition_stability`, abelian, IA-based) | its content (0A4D) sits inside the **sorry of `hasTorsionBaseChange_of_projectiveLine_of_isProper`**; that docstring says the property "composes and cancels along proper surjections". No own name | **used** (inside the §3 sorry, unnamed). Stays under prop-weil-pbc-reduction-to-projective-line. If that node is retyped to Λ-complexes (§3), retype this one to `HasTorsionBaseChange Λ`; its proof can then be a direct derived pasting with no IA |
| lemma-weil-pbc-cancellation (`hasTorsionAbelianBaseChange_of_comp_of_surjective`) | 0A4C, the same sorry ("cancels along proper surjections") | **used** (inside the §3 sorry). For Λ it needs IA in the Λ/ℓ form (option (d) of §2), or stays abelian if §3 goes by the abelian route |
| lem-weil-pbc-reduction-projective-space (`hasTorsionAbelianBaseChange_projectiveSpace_of_projectiveLine`) | the same sorry ("the finite surjective symmetric-product morphism (ℙ¹_S)ⁿ ⟶ ℙⁿ_S passes the hypothesis from ℙ¹ to ℙⁿ") | **used** (inside the §3 sorry). Purely formal from finite, composition and cancellation, so it carries over to any coefficients once those are retyped |
| lemma-weil-pbc-torsion-assembly (`isIso_derivedBaseChangeMapPlus_torsion_assembly`) | **bypassed**. The Lean target is `hasTorsionBaseChange_of_isProper Λ f sq K hK`: `HasTorsionBaseChange` already covers every complex with torsion cohomology for every proper f, so no "prime → n-torsion → colimit" step exists at a general f. That dévissage appears in Lean only for ℙ¹, inside `hasTorsionBaseChange_of_hasInjectiveAcyclicity` (its docstring) | **pruned.** It is also **redundant inside the DAG**: its conclusion (Ex_{□,F} an iso for every torsion abelian F and proper f) *is* PBC(f) of def-weil-pbc-property. thm-weil-pbc-bounded-below step 2 already has that from prop-weil-pbc-reduction-to-projective-line + prop-weil-pbc-projective-line, and lemma-weil-pbc-prime-proper-base-change only specialises it to 𝐅_r for torsion-assembly to rebuild. Replacement: thm-weil-pbc-bounded-below steps 3–4 cite "PBC(f) [def-weil-pbc-property], step 2" directly. On the Lean route the whole of steps 2–7 becomes "`hasTorsionBaseChange_of_isProper` applied to K" (lemma-weil-pbc-prime-proper-base-change, whose record is that declaration, retyped to Λ-complexes). Its other citer, prop-weil-proet-finite-proper-base-change, is `imported`; check that it is out of scope before deleting the node |

### 7. Consequences for stage 3

- **Statement or record changes on nodes:**
  - lem-weil-pbc-injective-acyclicity-bounded-below: the node ≠ the Lean (hypothesis differs). Either the Lean changes ((b) or (d), the human's decision) or, under (c′), the node's `lean` is re-pointed to a new "sheaf-level PBC_Λ ⇒ complex PBC_Λ" lemma (its steps 2–6), with a statement_change dropping the IA hypothesis.
  - lemma-weil-pbc-property-iff-acyclicity: record only. Drop the upstream sorry and point to the Sheaf iff; the statement is unchanged.
  - prop-weil-pbc-reduction-to-projective-line: re-encoded (Λ, complexes). Either a statement_change to Λ-complexes (then also the four nodes of §6 and target locality), or keep it abelian and add the G1 + G6 lift nodes, with the declaration proved unconditionally.
  - exists_addEquiv and the two curve declarations: **no statement change**. Their nodes prove the Lean once bridges are added.
- **Extra Sheaf nodes needed:**
  - (N1) G1: `forget₂` commutes with `upperStar`, with `R+ lowerStar` on D⁺, and with the exchange map, and is conservative. Needed by all five.
  - (N2) G2: `IsTorsionSheaf F ↔ IsTorsionAbelianSheaf (forget F)`.
  - (N3) G3: `Sheaf.H ≅ R^qΓ`, natural and compatible with `cohomologyMap`, unless the DAG settles on `Sheaf.H`.
  - (N4) the Λ-typed 0DDE lift: sheaf-level torsion PBC_Λ implies complex PBC_Λ.
  - (N5) the purely inseparable step and the σ/τ alignment for §1.
  - (N6) only if the Lean route keeps Λ throughout: Λ-complex versions of composition, cancellation, ℙⁿ reduction and target locality, and the Λ/ℓ change of rings for IA.
- **Order:**
  1. N1 and N2 first; everything uses them.
  2. The curve pair (§4, §5): closest to the Lean, bridges only.
  3. §1 (bridges plus N5).
  4. §2 and §3 wait for the human's choice (HUMAN.md 10-09/10-10; stage3-prep §4 item 2). Recommendation: (c′) for §2, which removes that sorry from the route at the cost of N4. For §3, decide Λ-throughout (N6) against abelian plus lift (N1 and N4, plus Sheaf imports in an upstream proof, which runs into the §2.1 module blocker unless option A or B is taken).
