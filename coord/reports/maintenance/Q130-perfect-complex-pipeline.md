# Q130 maintenance: perfect-complex stage-1 delivery

Item: `def-pod-perfect-complex-on-x`, dispatcher key
`def-pod-perfect-complex-on-x@new`. Maintenance workspace on the launcher:
`/home/ubuntu/weil-launcher-all/maint/Q130-def-pod-perfect-complex-on-x-1792196800`.

## Cause and evidence

The first attachment proposal was correctly rejected by an independent reader
at 2026-10-17 07:02:49 +08: the proposed ordinary discrete-coefficient Lean
predicate does not state all completed coefficient stages of the item. No
server attachment was attempted and no target return or delivery exists in
`coord/returns` or `coord/deliveries.log`.

The worker subsequently completed a definition split but repeatedly failed
mechanical preflight. Run `1792191778` received `blueprint_snapshot` maintainer
field errors twice. Packaging used the enumerated `MAINTAINER` denylist while
the authoritative contract treats **every** field outside `SPLIT_OWNS` as
maintainer-owned. The denylist omitted `blueprint_snapshot`, so stale sandbox
metadata could be copied into the delivery and then correctly rejected.

Run `1792194507` received both `HEAD is not on top of origin/newtargets-dag`
and an out-of-scope change to `coord/blueprint-index.tsv`, which the worker had
not edited. Local delivery worktrees share remote refs. A different worker's
fetch could advance `origin/newtargets-dag` after checkout or even between
resolving the preflight base and creating its bundle. The tools were comparing
the delivery against a moving ref rather than the checkout used to build it.

From run `1792196096` onward, the logs repeatedly terminate with provider HTTP
429 errors, including request IDs, while no last-answer file is written. The
dispatcher records blank `NOANSWER` and restarts. This is a separate provider
recovery issue repaired concurrently by maintenance for
`NK/lem-coef-mapping-simplex-final-edge`, server commit `a1a68055f2` (bounded
retry and session recovery, installed in the launcher CLI wrapper). This
change does not overwrite that work or lower concurrency, reset failure
counts, or suspend dispatch.

## Changes

- `tools/launcher/deliver.py`: shared `merge_split_node` helper uses the
  authoritative split-owned top-level and blueprint keys. Existing unknown
  metadata is retained from the base; new-node creation/source metadata is
  preserved. Capture the checkout SHA and pass it to preflight as `--base`.
- `tools/launcher/srvpreflight.py`: resolve an explicit base once, or recover
  the actual branch point with `git merge-base HEAD origin/<main>` for older
  callers. Bundle exclusion, transport, server validation, and local fallback
  use the same SHA. Multiple delivery commits remain visible to preflight.
- `tools/launcher/srvcheck.py`: reuse the same overlay helper for diagnostic
  checks, so checking and packaging use the same field-ownership contract.
- `tools/launcher/test_stage1_packaging.py` and
  `tools/launcher/test_preflight_base.py`: regression tests using the actual
  node contract, real temporary Git repositories/bundles and fake SSH.
- `tools/launcher/route-notes/def-pod-perfect-complex-on-x.md`: preserve the
  attachment rejection and explain how to resume the existing sandbox.

Runtime copies on the launcher are installed at
`/home/ubuntu/weil-launcher-nt/deliver.py` and
`/home/ubuntu/weil-launcher-all/{srvpreflight,srvcheck}.py`. All replaced files
have `.maint-Q130-1792196800.bak` siblings. New tracked files have backup
snapshots with the same suffix. No Lean file, mathematical node, claim,
dispatcher state, or failure count was changed by this maintenance.

## Validation

Nine new regression tests pass. The original `srvpreflight.py` fails the
same ref-race test: the transported base is the newer unrelated main commit.
Tests cover a main ref moving before preflight and between base resolution
and bundle creation, explicit SHA and ref forms, local fallback pinning,
unknown metadata absent/present on the base, new-node creation evidence, and
visibility of two delivery commits. They run no model or Lean command.

The real item's normal server dry run is also being checked. Its final result
and this maintenance commit SHA are recorded in the workspace `REPORT.md` and
evidence files. This maintenance does not deliver or mathematically approve
the split; the normal fresh second reader and maintainer review still apply.

## Successful real-item replay

At 2026-10-17 08:52:39 +08, the normal launcher command
`python3 /home/ubuntu/weil-launcher-nt/deliver.py Q130 def-pod-perfect-complex-on-x --no-push .`
passed server preflight and exited 0:

```text
OK (not pushed) deliver/Q130/def-pod-perfect-complex-on-x at 64ee1580ab: preflight passed
```

The immutable base was `93af03cb3cbb9109da85ce61a28131388b91d5cc`.
Server slot 0 recorded `rc=0 wait=0.0s run=54.2s`; the full replay output is
`evidence/item-dry-run.txt` in the maintenance workspace. The installed server
suites passed all nine new and six existing delivery-admission tests. The
Q130 tool fix is commit `783eefd22616654c6d85f4f5f7d107772caa9533`.

The active worker was editing the sandbox independently during maintenance.
This result validates the snapshot packaged by this replay, not future edits,
and does not replace the fresh second reader or the maintainer's mathematical
review. Nothing was pushed for the item.
