# Maintenance report: lem-sf-native-proper-projection-realization

Status: **cause confirmed; production repair requires the launcher-owned landing-tool maintainer**.
The task explicitly prohibits editing "the review service and the landing tools" and
requires describing the needed change here instead. `tools/nt_parallel2.py` is the
stage-2 landing preparation/commit tool. No protected code has been changed or bypassed.

## Cause

The five retries are the same deterministic tool failure, not a statement or proof-plan
failure. The retained, previously compiled delivery implements the theorem-module split
offered by the earlier review to avoid a future proof-import cycle. It removes
`AlgebraicGeometry.WeilComplex.native_compact_projection_formula` from
`Sheaf.Paper.NativeCompactProjectionFormula` and declares it once in
`Sheaf.Paper.NativeCompactProjectionFormulaTheorem`. The direct theorem consumer imports
the latter; the proper-projection modules import only the original definitions module.
Restoring or renaming the theorem would not repair this tool defect.

On server HEAD `909a4a20313f5d819551c923397af11f3fec60e2`, the two faulty phases are:

1. `tools/nt_parallel2.py:143`–154, `Preparation.prepare`: the delivered declaration and
   statement origins are unioned with `INDEX` using `ChainMap`. Origins removed from
   touched modules survive. Names removed entirely also fall through to the base index.
2. `tools/nt_parallel2.py:340`–349, `commit`: `prune` checks each delivered module against
   the unmodified base index, then the update only adds origins. Fixing preparation
   alone therefore leaves the commit phase rejecting the same valid move.

`tools/import_prune_check.py:97` correctly rejects two declaration origins in the index
it is given; it should not be weakened. The error is the caller's representation of the
effective source tree. The existing `tools/nt_batch2.py:157`–182 `SourceIndex.refresh`
already demonstrates removal semantics for a single on-disk module, but cannot be
called against delivered sources before they exist on disk.

Evidence checked: dispatcher state and all five retry notes; retained sandbox report
and five Lean sources; server `coord/returns/NA.md:86`; archived delivery
`95e62c1f9e07d783e024c922a51ae17f4e8255b3`; and
`/home/ubuntu/cc1/autoland.log:47557`, which records the exact duplicate-name refusal.
The same class of failure previously rejected extraction of the definitions at
`e234cae0e823cb5a5da11dd7f519c3e0d63fe025` (landing log line 47540).

## Verified repair specification (not installed)

Build one independent candidate source index for **all modules in a delivery before
any of that delivery's prune checks**, in both phases. For touched module set `T`:

```python
effective_decls[q] = (base_decls.get(q, set()) - T) | delivered_origins[q]
effective_statements[s] = {
    (q, mod) for q, mod in base_statements.get(s, set()) if mod not in T
} | delivered_statement_origins[s]
```

Apply this to every old key owned by a touched module and every new key, including
keys whose resulting value is empty. Empty entries must mask any `ChainMap` fallback.
Replace touched import entries and rebuild their `by_module` entries as well. Retain
origins in untouched modules so genuine collisions are still rejected.

Use a copy or copy-on-write sets: a failed candidate must not mutate the shared index.
In commit, run checks against the complete candidate and adopt it only after acceptance;
subsequent accepted plans must see the accumulated accepted view. Rejected, conflicting,
or later filtered plans must not contribute origins to the final accepted view. Do not
write delivery sources first, suppress duplicate checking, or delete the base cache as
a workaround. No concurrency, admission, timeout, dispatch, or provider change is needed.

An executable reference implementation and regression reproduction are retained in this
maintenance working directory as `reproduce_index.py`, with input
`delivery-snapshot.json` and output `reproduction.txt`. Copies of the script and input
are on the server in `/tmp/maint-na-projection-1793133166/`. To reproduce on the server:

```sh
cd /tmp/maint-na-projection-1793133166
PYTHONDONTWRITEBYTECODE=1 python3 reproduce_index.py delivery-snapshot.json
```

This only reads production tools and sources, refreshes a cached index **in memory**,
and invokes the existing prune checker against temporary files. It neither prepares
a production delivery nor changes a production index or ref.

## Validation

Executed against live server tools on 2026-10-28 about 04:35 Asia/Shanghai
(2026-10-27 20:35 UTC). The cached index was refreshed for 120 source changes in memory.

- Live declaration origins: `{Sheaf.Paper.NativeCompactProjectionFormula}`.
- Delivered old module has no theorem; delivered new module has the theorem.
  The old/new lexer-extracted theorem statements are equal.
- The current preparation union produces both origins and the real checker rejects it
  with the exact recorded error. The current commit/base view rejects it likewise.
- With the reference replacement overlay, **all five real module prune checks pass**.
- Tests also pass for unchanged-base isolation, matching statement origins, reversed
  delivery order, deletion without replacement, rejection of a duplicate in an
  untouched module, rejection of two delivered duplicates, and rejected-view isolation.

These are source-index/checker tests, not an end-to-end landing or independent
mathematical review. No Lean source changed, so no new Lean compilation was required.
The worker's earlier per-file compilation and successful preflight/dry run remain
historical evidence in its report; they are not claimed as new maintenance runs.

Protected tool hashes after reproduction (also recorded in `reproduction.txt`):

```text
1a3f22d3571128b73f9e29fc12b09aaaa6fff424f08a8b8d08870818d71eaaf0  tools/nt_parallel2.py
4961c005b02d0063985e313376012ee1df24659c2a846edf212eef4ea79be1f9  tools/nt_batch2.py
ecdf91c76dba2793e2f85b4b00ddb96079d7cfc3e9df6db30101421d1b101d03  tools/import_prune_check.py
```

## Changes and handoff

- Created this `REPORT.md` and the three local reproduction artifacts above.
- Added a brief-data handoff at
  `/home/ubuntu/weil-launcher-all/batch2/route-notes/lem-sf-native-proper-projection-realization.md`
  so future workers receive the verified diagnosis and preserve the valid module split.
- Published the diagnostic report at server path
  `coord/reports/maintenance/NA-lem-sf-native-proper-projection-realization-1793133166.md`.
  The local final report records its commit below.
- Kept `.bak` copies of created files; any pre-existing handoff file was backed up before
  replacement. The sandbox, DAG, source modules, claims, dispatch state, review/landing
  programs, compilation limits, and delivery refs were not changed.

Next worker: preserve the retained five-file repair and its existing definition-owner
nodes. This finding does not justify a `statement_change`, a mathematical re-plan,
renaming a declaration, restoring the import cycle, or an unchanged re-push. Check
whether both index phases have been corrected; after that, rebase the retained packet
against the current server, run the ordinary dry run and independent review/delivery.
The launcher-owned tool maintainer must apply the above replacement semantics. Dispatch
has not been stopped, limited, or paused, and the failure count has not been reset.
