# G8 maintenance: CompactificationUpperShriek

Item: `WeilConjectures.SixFunctors.Etale.Derived.CompactificationUpperShriek`, stage 3.
Project: `/home/ubuntu/weil-conjectures-sheaf` on `ubuntu@the project server`.

## Cause

The dispatcher repeatedly received an unused source module from a stale proof-route fallback.
The missing DAG attachment reported by the workers was a symptom, not the dispatch trigger.

1. Upstream sync `f90ec68101` restored the legacy
   `AlgebraicGeometry.Etale.CompactificationUpperShriek` namespace, including its one
   general-coefficient adjoint-existence `sorry`, after its earlier retirement.
2. The saved complete route still used build `78af1b290415df2aac5be390b10bac3e40a5179e`
   (`t = 1792478412.6979532`). The item was absent from that route. Nevertheless,
   `tools/queue.py:stage3` conservatively added source files changed since that build.
   The restored module therefore appeared as stage 3, import distance 8, one sorry, `proof/route`.
3. Later walks successfully refreshed batch 5 against build
   `b8d83fa1c768252d75fef65132539a57952aae23`, again without using this namespace.
   But missing compiled artifacts in batches 2–4 made `tools/sorry_route.py` reject the
   entire new route. Their errors included `RhomGlobalSectionsOfUniverses.olean`,
   `FiniteOrderedCechCoefficientMap.olean`, and `ConstructibleShiftSingle.olean`.
   Successful batch-5 data was left only in `local/sorry-route-failed.json`.
4. Every retry consequently received the same irrelevant general-coefficient obligation.
   The old purported supporting lemma had already been corrected on 2026-10-18 to finite
   module coefficients on Noetherian quasi-compact schemes; it does not supply this instance.

All 12 completed G8 attempt records inspected had `status: answered`, `recoveries: 0`,
and an empty `last_error`. This failure sequence was not caused by a provider error.

## Changes and commits

Server code commit: **`673b8c7003` — Refresh successful sorry-route batches independently of failed walks**.
Committed as Bin Wu <844524296@qq.com>, with `SHEAF_LEAD=L-only` under `coord/.merge.lock`.

- `tools/sorry_route.py`: publish successful batches while retaining each failed batch's
  previous complete route. Record `batch_commits` and `batch_times`, preserving the older
  baseline across repeated failures. Keep failure diagnostics and a nonzero exit status.
  Respect an explicitly supplied `SHEAF_TOOL_TIMEOUT`; this maintenance run used 60 seconds.
- `tools/queue.py`: compare source changes against each batch's own baseline, within that
  batch's current import closure.
- `tools/tag_batches.py`: use the corresponding batch baseline when assigning tags.
- `tools/test_sorry_route.py`: six regressions covering partial refresh, repeated failure,
  missing prior data, retained reporting, real Git source changes and legacy timestamp fallback.
- `tools/test_queue.py`: adapt its route mock to the batch-aware source-change helper.

Refreshed generated state: `local/sorry-route.json`, `local/sorry-route-failed.json`,
`local/stage3-reach.json`, `coord/queue.tsv`, `coord/queue.md`,
`coord/queue-batches.tsv`, `coord/queue-batches-all.tsv`, and the queue-generated
`coord/blueprint-index.tsv`. Existing generated Lean probes were backed up before regeneration.
These generated files were not staged with the code or with unrelated working-tree changes.

Backups of existing edited tools and runtime state are adjacent files ending
`.maint-G8-1792508145.bak`. Local source backups are in `repair/tools/*.bak` in the
maintenance working directory. A mirror snapshot of the generated blueprint index is
also retained as a `.bak` file.

No Lean declaration, DAG statement, public import, retry counter, launcher-owned file,
review service or landing tool was changed. No concurrency control was added and no
existing process was killed.

## Verification

- Eight regression tests passed on the server: six route tests and two queue tests.
  The source-baseline test uses real Git commits and verifies that new/untracked work remains
  eligible, failed batches retain their work, and successful batches discard stale changes.
- Ran `SHEAF_LEAD=L-only SHEAF_TOOL_TIMEOUT=60 python3 tools/sorry_route.py`.
  Lean probes ran sequentially through `tools/lean_file.sh`, with a 60-second limit each.
  The command returned 1 for the existing missing-artifact errors, but correctly published
  the successful batch-5 refresh and retained the earlier complete batch-2/3/4 routes.
- Batch 5 advanced to `b8d83fa1c768252d75fef65132539a57952aae23`; failed batches kept
  `78af1b290415df2aac5be390b10bac3e40a5179e`. Their retained route contents were checked
  against the pre-maintenance snapshot.
  The following automatic refresh independently advanced batches 2 and 5 to
  `b4b2629c02bb539047bb85952fbe76bda713becf`, while batches 3 and 4 retained their old
  routes. The final `verification.json` records that later state.
- Regenerated the queue under the merge lock, then its batch tags. The item is absent from
  `coord/queue.tsv`, `coord/queue-batches.tsv`, and `coord/queue-batches-all.tsv`.
  It is neither on the target proof route nor a source change in any relevant batch.
- The source module still has its original one `sorry`; its SHA-256 is
  `8c23053ad1a99ef73829597671b5771caa670ac888bc062887d6ea4f1f74b7b7`.
  No proof progress is claimed. No `lake build` was run.

Server evidence: `local/maintenance/G8-CompactificationUpperShriek/route-refresh.log`
and `verification.json`. Copies of the refresh log, before/after route snapshots, and
verification are under `repair/evidence/` in the maintenance working directory.

## Next worker

This legacy module has no current target proof obligation. Its declarations remain in the
adopted source library; preserving them does not require dispatching unused holes.
An already-running worker was left running. No fresh mathematical delivery is needed for
the stale assignment.

If this item is dispatched again, first inspect the live queue and proof route. A future
source change could make it needed; that would require a source-supported plan for its
actual general-coefficient hypotheses. Do not reuse the retracted general-coefficient
lemma, substitute its finite-coefficient correction, retire the restored declarations,
or move the original obligation to an equivalent fresh `sorry`.

The missing-artifact problems in batches 2–4 remain visible and retain their earlier
route baselines. They no longer prevent a successful batch-5 refresh. Launcher-owned
changes are unnecessary for this fix.
