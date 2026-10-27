# Q71 maintenance: gerbe diagonal descent

2026-10-24; item `lem-sfb-gerbe-qc-diagonal-descent`, stage 2;
returned dispatcher key `lem-sfb-gerbe-qc-diagonal-descent@39d8339d0`.

The H4 return required `Sheaf.AlgebraicGeometry.GerbeModuliMap` /
`def-sfb-gerbe-moduli-map`, but neither existed on main. They were in Q117's
approved delivery `274c557c1a93c425cd6e67a6a1f4405014fc91be` for
`lem-sfb-gerbe-smooth-universal-homeomorphism`. Its independent review passed
at 14:27:10 +08 (reviewer `NT-stage2-cc-274c557c1`). The review service log
subsequently shows landing retries at 19:24:57 and 21:03:09 with
`batch heads changed before write`, and at 20:02:55 with
`delivery or compile dependency changed`. Q71 could not satisfy its return
until this approved prerequisite actually landed; repeating its correct repair
could not resolve missing server data.

Used the existing `tools/nt_land2.py` single-delivery path with that recorded
PASS, after a successful dry run and .bak backups. The first attempt compiled
the definition but stopped because the L mirror and published build lacked
`AlgebraicStackFibreProducts.olean`, although its source existed. Rebuilt that
unchanged source with `SHEAF_GROUP=L tools/lean_file.sh` (8.1 s). Took out the
partial landing `20261024T133654-L-2840183` using the prescribed landing tool
(commit `1c0a5dc64da`), then retried the approved delivery. It merged as
`bb8bae630b22718d7ebc2e89c376a904160b98ec` under the merge lock, as Bin Wu.
No mathematics or theorem signature was changed.

The successful delivery added the canonical definition node and both modules:

- `dag/nodes/sec-six-functors-basics/def-sfb-gerbe-moduli-map.json`
- `lean/Sheaf/AlgebraicGeometry/GerbeModuliMap.lean`
- `lean/Sheaf/AlgebraicGeometry/GerbeSmoothUniversalHomeomorphism.lean`

It updated the Q117 item's node, committed its report, and performed the
normal claim/ledger/deliveries bookkeeping. Existing affected files were
backed up with `.maint-Q71-gerbe-1792848096.bak` or
`.maint-Q71-gerbe-retry-1792848096.bak` suffixes. Main's existing global build
observed the first attempt during its failure cleanup (build `be726382035`);
the explicit take-out and successful complete retry are the authoritative
subsequent sequence.

Validation: Q71's retained canonical import, hypothesis, owning stmt_dep and
verbatim lean.statement were checked. `batch2/scompile.py` succeeded, and
`batch2/deliver2.py --no-push` returned a clean compile/preflight pass
(`aa5f2df1e6b`). The active Q71 worker independently passed its checks and
pushed `deliver/Q71/lem-sfb-gerbe-qc-diagonal-descent` at `98163b28119`.
Its independent review and normal global build verification remain pending.
Do not restore the duplicate `IsGerbeOver` / `GerbeOver.lean` or re-push an
unchanged packet; continue from the delivered repair and its next review.

Launcher-owned landing/review tools were not edited. A follow-up repair of
`tools/nt_parallel2.py` is needed: the `changed_heads` branch currently empties
all ready plans when any delivery branch changes; it should retire/retry the
changed plan and preserve the unaffected survivors under the existing guards.
The evidence and suggested change are also in the launcher's maintenance
`REPORT.md`. No concurrency/admission settings or provider behavior changed.
