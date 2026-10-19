# Maintenance: retain the derived-system dependency interface repairs

The repeated failure of `lem-coef-derived-system-evaluation-calculus` was caused
by unpromoted dependency records. It was not an SSH, compiler, permission, or
failure-count problem. The actual pro-etale site has objects in universe `t+1`
and arrows in `t`; its completed coefficients have size `max (t+1) u`. The
legacy single-universe dependency signatures cannot accept these arguments.

Earlier side commits already supplied and checked the necessary companions:
`33198b9a19c5f79a1dbdc66987930c0e0308aac6` for the strict tower limit, and
`5eb8234f79583ab3c07539b41be7cac2acd0dd66` for zeroth hypercohomology and
derived Hom global sections. Those maintenance commits were never promoted
to the authoritative shared DAG. Consequently ordinary live-DAG refreshes
`33c9f8d822` and `b147d54ce5` restored the legacy `lean` records. The worker's
bottom-up brief then correctly prevented a prerequisite restatement in its
own delivery. Repeating the same worker could not retain the side-only repair.

`coord/sheaf.env` points `SHEAF_DAG` to the shared live DAG. The synchronizer
deliberately imports its Lean records. The durable repair is therefore a
shared DAG promotion, as already documented in `coord/dag-sync.md`; no change
to the synchronization policy or worker brief is necessary.

## Changes and commits

Used the existing `tools/nt_land2.py` promotion function to promote ONLY the
three previously checked `lean` fields to `/home/ubuntu/weil-conjectures-sheaf`:

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-ringed-strict-tower-homotopy-limit.json`
  in shared commit `a7f4eceb09d29f6ef2819d6d3288070e847cd3ff`.
- `dag/nodes/sec-smooth-purity/def-pur-ringed-site-zeroth-hypercohomology.json`
  and `dag/nodes/sec-smooth-purity/lem-pur-rhom-global-sections.json`
  in shared commit `c5fce1c3f13eb39f74e4027bc2e9eda9fdd389c2`.

The normal promotion and merge locks guarded the operations. Commits use
`SHEAF_LEAD=L-only`, `Bin Wu`, and `844524296@qq.com`. The original node
statements, proofs, graph edges and reviews are preserved. The comparison
companion is still a stage-2 statement with `sorry`; the historical V4 proof
belongs to the legacy comparison, as the promoted record explicitly explains.

Ran the actual `tools/sync_newtargets.py` synchronization after promotion.
Side commit `0df7c9458485fed38c1205fb5bfeff6fbc91e54c` imports and retains all
three repaired bindings. Its normal refresh also imported the independently
changed `cor-amb-affine-space-adjunction` record, advanced `coord/live-dag-tip.txt`,
and wrote the synchronizer's ledger/claim-retirement events. All existing
files written or removed by this invocation were backed up beforehand.

Backups in both server repositories append `.maint-NZ-1792137780.bak` to
each changed record. The side synchronization's written records, ledger,
tip file, cursors and existing claims have the same backup suffix. This new
report also has a backup. Promotion receipts are retained at
`local/stage2/shared/<original-side-commit>.json`.

No Lean source, live artifact, target statement, tool implementation or
dispatcher state was changed. No process was stopped. No Lake build ran.

## Validation

Recompiled each existing companion through `tools/lean_file.sh`, sequentially:
zeroth hypercohomology in 1.3 seconds, derived Hom comparison in 1.8 seconds,
and strict tower limit in 1.9 seconds. Dependencies were compiled sequentially
into the private overlay too. Every Lean invocation retained nice 19, two
threads, and the hard 60-second limit.

The retained actual-site regression probe
`lean/.sandbox/maintenance-NZ-1792135887/RhomIndependentUniverseProbe.lean`
compiled in 2.2 seconds. It applies both companions to the actual completed
coefficients with independent `t` and `u`, consumes the natural additive
equivalence on arbitrary derived inputs, and checks that the legacy APIs
remain visible. No error or warning was reported.

Before promotion, checked that each earlier commit changed only the node's
`lean` field and that its recorded signature occurs verbatim in its unchanged
companion source. After the real synchronization, checked all three bindings
in both committed HEADs and working trees, plus clean status for those paths.
The promoted DAG diffs pass `git diff --check`.

## Next worker and future maintenance

Read the refreshed shared records. Import
`Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses` and
`Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses`.
Use `rhom_global_sectionsOfUniverses.{t + 1, t, u}` with
`Scheme.ProEt.topology Y` and `completedIntegralCommRingSheafUnrestricted l E Y`.
Use `ringedSiteZerothHypercohomologyOfUniverses` and
`derivedInternalHomOfUniverses` at the same arguments. Supply the standard
derived-category localization instance for the exact module category, as in
the retained probe. The fourth universe parameter chooses that localization.

The legacy `RhomDependencyProbe.lean` deliberately calls the old theorem and
will continue to fail on this site. `CurrentRhomDependencyProbe.lean` and the
retained regression probe exercise the repaired API. Do not equate the site
object and arrow universes or restate these prerequisites in the item delivery.
The item's own mathematics and stage-2 delivery remain the worker's task.

Future maintenance that repairs a side DAG interface must finish the same
shared promotion as an ordinary stage-2 landing (`tools/nt_land2.py --promote
<side-commit>`), under its promotion and merge guards. A side-only commit is
not a completed shared-record repair. Back up the authoritative records
before promotion and check a subsequent live-DAG refresh. Historical failure
counts should remain historical; this repair does not change dispatch eligibility.
