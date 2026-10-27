# NQ maintenance: lem-pur-iterated-purity-scalar-pasting

Fixed: the normal delivery dry run now compiles and passes preflight at `41af058124f`. The repeated failure came from a landed dependency regression, compounded by a stale client result cache. The item's statement and proof plan did not need changing.

## Cause

`f9b5bc8dbe3` changed `AffineZeroPurity.target` in `lean/Sheaf/Paper/AffineSpaceThomMap.lean` from `AffineSpacePurity.tensor` to the equivalent `curriedTensor` with the shared `cupMonoidal` instance. `AffineSpaceZeroSectionPurity.lean` locally marks `AffineSpacePurity.tensor` irreducible. Consequently, its `targetPullbackIso` construction could no longer unify the two presentations when rebuilding current committed dependencies. This is the error at line 454 in overlay snapshot `5faf8727177a18f3de2004ae62711b2139d001b92ca21d7725b36995b92b23a4`.

The review's apparently conflicting observation is explained by the build state. `local/builds/published.json` still identifies green commit `944629df7b1515f962bb864974de3388fce141a8` (2026-10-25 20:08:46 UTC). The newer changed dependency sources are selected by `tools/nt_source_overlay.py:committed_modifications`. The published oleans' recent mtimes do not establish that they contain these later sources. An isolated compile against published dependencies succeeded in 52.7 seconds, while the worker's current-source overlay failed. Thus this was a real dependency implementation regression, not evidence that the worker should create duplicate interfaces.

Separately, `batch2/scompile.py:run_many` keys its saved result by worker file contents and `CA.published_stamp()` only. A dependency repair committed while the global build remains red does not change that key. Five retries therefore returned the same old failure before reaching the repaired item.

## Applied repair and commit

Server project: `/home/ubuntu/weil-conjectures-sheaf`, branch `sheaf-dag`.

Commit `6010549ca6030b58846dbe6e733a80f2b3e5011c` changes only:

- `lean/Sheaf/Paper/AffineSpaceZeroSectionPurity.lean`: explicitly unfold `target`, `AffineSpacePurity.tensor`, and `derivedTensor` when applying the existing `actionPullbackIso` construction. The signature, isomorphism factors, docstring, and existing transparency settings are preserved. No theorem, axiom, sorry, node, or mathematical hypothesis is added.

The commit ran under `SHEAF_LEAD=L-only flock coord/.merge.lock`, with identity `Bin Wu <844524296@qq.com>`. Its exact staged set was printed. Other agents' working changes were excluded with an explicit-path commit.

After committing the source repair, backed up and invalidated exactly these two obsolete result-cache files under `/home/ubuntu/weil-launcher/compile-results/`:

- `see6246392a2c54826726f029-72858d1c4838923ae74299cc.json` (ordinary item compile).
- `sec66125a2fe311e9e3cbaac5-72858d1c4838923ae74299cc.json` (delivery compile).

Both were verified to contain exit 1 and the old `AffineSpaceZeroSectionPurity.lean:454` error before invalidation. Their `.bak.NQ-maint-1792969241` copies remain. No runner state, dispatcher state, other task cache, or process was removed.

## Validation

- Current dependency overlay: sandbox 52.5 seconds, library module 54.1 seconds, exit 0, no warnings (`repaired-overlay-zero-section-pass2.log`).
- `SHEAF_GROUP=NQ-maint-overlay-1792969241 tools/lean_file.sh lean/Sheaf/Paper/AffineSpaceZeroSectionPurity.lean`: exit 0, 56.3 seconds (`repaired-lean-file.log`). This isolated mirror uses the exact current overlay artifacts captured from the preceding compile, rather than the older published dependency artifacts. Acceptance remained 60 seconds; the configured diagnostic run limit was not changed.
- `git diff --check` and Lean line-width checks passed.
- The proposed client cache repair passes four regression tests, including invalidation after a committed dependency changes while publication is unchanged, stable reuse for unchanged dependencies, and refusal to reuse a cached answer when current server state cannot be read.
- The active worker's ordinary two-file `scompile.py` request returned exit 0: compositor sandbox/library 18.2/14.2 seconds; item sandbox/library 28.5/31.2 seconds (`successful-item-scompile.log`).
- Ordinary `deliver2.py NQ lem-pur-iterated-purity-scalar-pasting --no-push`: exit 0, `OK (dry run): commit 41af058124f passes the preflight and compiles; nothing pushed` (`delivery-dry-run.log`). My validation call and the worker's call attached to the same compile runner. The subsequent normal delivery compile used the committed repair and successfully rebuilt the affected dependency closure.

Every Lean invocation ran on one file at a time. No `lake build` was run and no process was killed.

## Protected launcher cache repair: owner action

The integrity service restored an attempted `batch2/scompile.py` change at `2026-10-26 07:05:31`, recorded in `/home/ubuntu/weil-launcher-all/integrity/incidents.log:993`. The deployed file is byte-identical to its pre-edit backup. I did not modify the integrity service or its baseline and did not reapply the protected edit.

The launcher owner should apply `scompile-dependency-cache.patch` through its normal deployment/integrity-baseline process. The tested proposal keys requests and results by current server `HEAD:lean`, `HEAD:tools`, and the published/last-build metadata, in addition to worker contents. Including dependency state in the request content prevents an already-running request against old dependencies from satisfying a repaired request. It reports an unavailable server state rather than replaying a stale cached failure. Full proposed source and four tests are in `proposed_client/`; run `python3 -m unittest -v test_scompile_dependency_stamp.py` there on the launcher machine.

This owner change is a permanent cache-correctness improvement; the committed dependency repair and targeted stale-result invalidation address this item's current blockage.

## Backups and next worker

Server source backups are beside the Lean file as `.bak.NQ-maint-1792969241` (original) and `.bak.NQ-maint-1792969241-pass1` (discarded initial experiment). The local compiler backup is `/home/ubuntu/weil-launcher-all/batch2/scompile.py.bak.NQ-maint-1792969241`; the proposal also retains its original as `proposed_client/scompile.py.bak`. Cache backups are listed above. Disposable build outputs and new evidence files are not source edits.

Continue with the retained sandbox and the normal compiler/delivery commands. Keep the H13/H4 repairs: use landed `RationalScalarComparisonData` and `AdicPurityScalarNaturality`, retain the dependency records, do not recreate either Interface module, and cite `def-pur-rational-scalar-comparison-data` as requested by H2. No statement_change or re-plan is needed for this build failure. Maintenance ran only the dry run and has not pushed or landed the item's delivery; its ordinary worker/reviewer owns that step. No launcher-owned control file needs editing to resume this item. The permanent cache-key improvement still requires the launcher owner, as documented above.
